#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/innards/product_bounds.hh>
#include <gcs/constraints/innards/product_encoding.hh>
#include <gcs/constraints/innards/product_justify.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/problem.hh>

#include <cstdlib>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif
#include <iostream>
#include <memory>
#include <optional>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::make_optional;
using std::make_shared;
using std::make_unique;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::tuple;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

using gcs::innards::product_justify::ConditionalBound;

namespace
{
    // Each fragment emits a small, self-contained piece of proof against the
    // cake multiply encoding, at the root, under domains the test has pinned
    // in advance. The point of the harness is that a wrong fragment fails
    // veripb in a test that contains nothing else, rather than deep inside a
    // full propagation proof.
    enum class Fragment
    {
        TrivialRup,    // emit an order-encoding bound as RUP: proves the wiring, nothing else
        ChannelBounds, // channel v1's live sign branches' bounds to its slot magnitude
        GridLower,     // subprocedure 7.1: grid_sum >= lb|x| * lb|y| on the positive branches
        GridUpper,     // subprocedure 7.2: grid_sum <= ub|x| * ub|y|, called twice to exercise the W-line cache
        ProductBounds, // procedure 7.5 end to end: both bounds on z via the sign-case driver
        FactorUpper,   // procedures 7.6/7.7: justify x <= q_hi by refuting the excluded range
        SquareBounds,  // aliased grid (both slots one variable): z >= 0 probe + driver square bounds
    };

    // The slot-keyed cake encoding handles the fragments work against.
    struct FragmentEncoding
    {
        product_enc::MagnitudeChannel chan1;
        product_enc::MagnitudeChannel chan2;
        product_enc::BitProductGrid grid;
        product_enc::ResultChannel zchan;
        vector<ProofLine> signs;
    };

    // Every ConditionalBound a fragment derives is restated crisply as a
    // checked implication citing the derived line. pol lines are sound by
    // construction whatever they compute, so without this a helper that
    // derives something other than what it claims would sail through; the
    // `ia` check is what makes a wrong fragment fail veripb.
    auto assert_claimed_bound(ProofLogger & logger, const ReasonLiterals & reason, const ConditionalBound & cb) -> void
    {
        logger.emit_under_reason(
            ImpliesProofRule{make_optional<ProofLine>(cb.line)}, logger.reify(cb.sum >= cb.rhs, cb.cases), ProofLevel::Temporary, reason);
    }

    // A test-only constraint: defines the real cake multiply encoding for
    // x * y = z via the slot-keyed emitters, runs one selected justification
    // fragment in an initialiser, and otherwise only rejects violating
    // complete assignments (which is RUP against the encoding), so that the
    // solutions the solver logs agree with the OPB while leaving every
    // intermediate derivation to the fragment under test.
    class ProductFragmentForTest : public Constraint
    {
    private:
        SimpleIntegerVariableID _v1, _v2, _v3;
        Fragment _fragment;

    public:
        ProductFragmentForTest(SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3, Fragment fragment) :
            _v1(v1), _v2(v2), _v3(v3), _fragment(fragment)
        {
        }

        [[nodiscard]] auto clone() const -> unique_ptr<Constraint> override
        {
            return make_unique<ProductFragmentForTest>(_v1, _v2, _v3, _fragment);
        }

        auto install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void override
        {
            auto encoding = make_shared<optional<FragmentEncoding>>(nullopt);
            if (optional_model) {
                auto label = as_string(constraint_id());
                auto naming = product_enc::LinkNaming{};
                auto chan1 =
                    product_enc::emit_magnitude_channel(*optional_model, initial_state, constraint_id(), label, "MultiplyBC", _v1, 0, "X", naming);
                auto chan2 =
                    product_enc::emit_magnitude_channel(*optional_model, initial_state, constraint_id(), label, "MultiplyBC", _v2, 1, "Y", naming);
                auto grid = product_enc::emit_bit_product_grid(*optional_model, constraint_id(), label, chan1.mag, chan2.mag, naming);
                auto zchan = product_enc::emit_result_channel(*optional_model, label, "MultiplyBC", _v3, grid, naming);
                auto signs = product_enc::emit_sign_clauses(*optional_model, label, "MultiplyBC", _v1, _v2, _v3, naming);
                *encoding = FragmentEncoding{chan1, chan2, grid, zchan, signs};
            }

            propagators.install_initialiser(
                [encoding = encoding, v1 = _v1, v2 = _v2, v3 = _v3, fragment = _fragment](State & state, auto &, ProofLogger * const logger) {
                    if (! logger)
                        return;
                    auto & enc = **encoding;

                    auto bounds_reason = [&](SimpleIntegerVariableID v) {
                        return ReasonLiterals{v >= state.lower_bound(v), v <= state.upper_bound(v)};
                    };

                    // Channel one operand's live sign branches to its slot magnitude.
                    auto channel_live_branches = [&](SimpleIntegerVariableID v, const product_enc::MagnitudeChannel & chan,
                                                     const ReasonLiterals & reason) -> vector<ConditionalBound> {
                        auto [lo, hi] = state.bounds(v);
                        auto ob_lo = product_justify::derive_operand_bound(*logger, reason, v, true, lo);
                        auto ob_hi = product_justify::derive_operand_bound(*logger, reason, v, false, hi);
                        vector<ConditionalBound> result;
                        for (auto negative_branch : {false, true}) {
                            if (negative_branch ? lo >= 0_i : hi < 0_i)
                                continue;
                            for (const auto & ob : {ob_lo, ob_hi}) {
                                auto cb = product_justify::channel_bound_to_magnitude(*logger, ob, v, chan, negative_branch);
                                assert_claimed_bound(*logger, reason, cb);
                                result.emplace_back(cb);
                            }
                        }
                        return result;
                    };

                    switch (fragment) {
                    case Fragment::TrivialRup:
                        logger->emit_rup_proof_line(WPBSum{} + 1_i * (v3 >= state.lower_bound(v3)) >= 1_i, ProofLevel::Top);
                        break;

                    case Fragment::ChannelBounds:
                        channel_live_branches(v1, enc.chan1, bounds_reason(v1));
                        channel_live_branches(v2, enc.chan2, bounds_reason(v2));
                        break;

                    case Fragment::GridLower: {
                        // positive-branch magnitude lower bounds for both slots,
                        // multiplied through the grid (7.1)
                        auto reason = ReasonLiterals{v1 >= state.lower_bound(v1), v2 >= state.lower_bound(v2)};
                        auto x_lb = product_justify::channel_bound_to_magnitude(
                            *logger, product_justify::derive_operand_bound(*logger, reason, v1, true, state.lower_bound(v1)), v1, enc.chan1, false);
                        auto y_lb = product_justify::channel_bound_to_magnitude(
                            *logger, product_justify::derive_operand_bound(*logger, reason, v2, true, state.lower_bound(v2)), v2, enc.chan2, false);
                        auto glb = product_justify::grid_sum_lower_bound(*logger, reason, enc.grid, enc.chan1.mag, x_lb, y_lb);
                        assert_claimed_bound(*logger, reason, glb);
                        break;
                    }

                    case Fragment::GridUpper: {
                        auto reason = ReasonLiterals{v1 <= state.upper_bound(v1), v2 <= state.upper_bound(v2)};
                        auto x_ub = product_justify::channel_bound_to_magnitude(
                            *logger, product_justify::derive_operand_bound(*logger, reason, v1, false, state.upper_bound(v1)), v1, enc.chan1, false);
                        auto y_ub = product_justify::channel_bound_to_magnitude(
                            *logger, product_justify::derive_operand_bound(*logger, reason, v2, false, state.upper_bound(v2)), v2, enc.chan2, false);
                        auto gub = product_justify::grid_sum_upper_bound(*logger, reason, enc.grid, enc.chan1.mag, enc.chan2.mag, x_ub, y_ub);
                        assert_claimed_bound(*logger, reason, gub);

                        // a second, tighter derivation reuses the cached W-lines
                        auto x_ub2 = product_justify::channel_bound_to_magnitude(
                            *logger, product_justify::derive_operand_bound(*logger, reason, v1, false, state.upper_bound(v1)), v1, enc.chan1, false);
                        auto gub2 = product_justify::grid_sum_upper_bound(*logger, reason, enc.grid, enc.chan1.mag, enc.chan2.mag, x_ub2, y_ub);
                        assert_claimed_bound(*logger, reason, gub2);
                        break;
                    }

                    case Fragment::ProductBounds: {
                        auto [xlo, xhi] = state.bounds(v1);
                        auto [ylo, yhi] = state.bounds(v2);
                        auto reason = ReasonLiterals{v1 >= xlo, v1 <= xhi, v2 >= ylo, v2 <= yhi};
                        auto [prod_lo, prod_hi] = product_bounds(xlo, xhi, ylo, yhi);

                        auto dims = vector<product_justify::SignCaseDimension>{{v1 >= 0_i, v1 < 0_i}, {v2 >= 0_i, v2 < 0_i}};
                        vector<optional<ConditionalBound>> lower_premises(4, nullopt), upper_premises(4, nullopt);
                        for (unsigned pattern = 0; pattern < 4; ++pattern) {
                            bool xneg = pattern & 1u, yneg = pattern & 2u;
                            if ((xneg ? xlo >= 0_i : xhi < 0_i) || (yneg ? ylo >= 0_i : yhi < 0_i))
                                continue;
                            bool zneg = xneg != yneg;
                            // magnitude lower bound: positive branch from the operand's lower
                            // bound, negative branch from its upper; uppers the other way round
                            auto x_mag_lb = product_justify::channel_bound_to_magnitude(
                                *logger, product_justify::derive_operand_bound(*logger, reason, v1, ! xneg, xneg ? xhi : xlo), v1, enc.chan1, xneg);
                            auto y_mag_lb = product_justify::channel_bound_to_magnitude(
                                *logger, product_justify::derive_operand_bound(*logger, reason, v2, ! yneg, yneg ? yhi : ylo), v2, enc.chan2, yneg);
                            auto x_mag_ub = product_justify::channel_bound_to_magnitude(
                                *logger, product_justify::derive_operand_bound(*logger, reason, v1, xneg, xneg ? xlo : xhi), v1, enc.chan1, xneg);
                            auto y_mag_ub = product_justify::channel_bound_to_magnitude(
                                *logger, product_justify::derive_operand_bound(*logger, reason, v2, yneg, yneg ? ylo : yhi), v2, enc.chan2, yneg);

                            auto glb = product_justify::grid_sum_lower_bound(*logger, reason, enc.grid, enc.chan1.mag, x_mag_lb, y_mag_lb);
                            auto gub =
                                product_justify::grid_sum_upper_bound(*logger, reason, enc.grid, enc.chan1.mag, enc.chan2.mag, x_mag_ub, y_mag_ub);
                            if (! zneg) {
                                lower_premises[pattern] =
                                    product_justify::channel_grid_bound_to_result(*logger, reason, v3, enc.zchan, glb, false, true);
                                upper_premises[pattern] =
                                    product_justify::channel_grid_bound_to_result(*logger, reason, v3, enc.zchan, gub, false, false);
                            }
                            else {
                                lower_premises[pattern] =
                                    product_justify::channel_grid_bound_to_result(*logger, reason, v3, enc.zchan, gub, true, false);
                                upper_premises[pattern] =
                                    product_justify::channel_grid_bound_to_result(*logger, reason, v3, enc.zchan, glb, true, true);
                            }
                        }
                        product_justify::conclude_by_sign_cases(*logger, reason, WPBSum{} + 1_i * v3 >= prod_lo, dims, lower_premises);
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (v3 >= prod_lo) >= 1_i, ProofLevel::Temporary);
                        product_justify::conclude_by_sign_cases(*logger, reason, WPBSum{} + -1_i * v3 >= -prod_hi, dims, upper_premises);
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (v3 <= prod_hi) >= 1_i, ProofLevel::Temporary);
                        break;
                    }

                    case Fragment::FactorUpper: {
                        auto [xlo, xhi] = state.bounds(v1);
                        auto [ylo, yhi] = state.bounds(v2);
                        auto [zlo, zhi] = state.bounds(v3);
                        auto qf = quotient_filter(ylo, yhi, zlo, zhi);
                        if (qf.kind != QuotientFilter::Kind::Bounds || qf.hi >= xhi) {
                            cerr << "FactorUpper fragment posted on domains where the filter does not tighten\n";
                            exit(EXIT_FAILURE);
                        }
                        auto q_hi = qf.hi;
                        auto reason = ReasonLiterals{v2 >= ylo, v2 <= yhi, v3 >= zlo, v3 <= zhi};

                        // x's bounds over the refuted excluded range (q_hi+1 .. xhi):
                        // the assumed atom is supplied as a unit by the negated goal.
                        auto x_lb_excl = product_justify::derive_assumed_operand_bound(*logger, v1, true, q_hi + 1_i);
                        auto x_ub_plain = product_justify::derive_operand_bound(*logger, ReasonLiterals{}, v1, false, xhi);
                        auto y_lb = product_justify::derive_operand_bound(*logger, reason, v2, true, ylo);
                        auto y_ub = product_justify::derive_operand_bound(*logger, reason, v2, false, yhi);
                        auto z_lb = product_justify::derive_operand_bound(*logger, reason, v3, true, zlo);
                        auto z_ub = product_justify::derive_operand_bound(*logger, reason, v3, false, zhi);

                        auto dims = vector<product_justify::SignCaseDimension>{{v1 >= 0_i, v1 < 0_i}, {v2 >= 0_i, v2 < 0_i}};
                        vector<optional<ConditionalBound>> premises(4, nullopt);
                        for (unsigned pattern = 0; pattern < 4; ++pattern) {
                            bool xneg = pattern & 1u, yneg = pattern & 2u;
                            if (xneg ? (q_hi + 1_i > -1_i || xlo >= 0_i) : xhi < 0_i)
                                continue;
                            if (yneg ? ylo >= 0_i : yhi < 0_i)
                                continue;
                            bool zneg = xneg != yneg;
                            auto x_mag_lb = product_justify::channel_bound_to_magnitude(*logger, xneg ? x_ub_plain : x_lb_excl, v1, enc.chan1, xneg);
                            auto x_mag_ub = product_justify::channel_bound_to_magnitude(*logger, xneg ? x_lb_excl : x_ub_plain, v1, enc.chan1, xneg);
                            auto y_mag_lb = product_justify::channel_bound_to_magnitude(*logger, yneg ? y_ub : y_lb, v2, enc.chan2, yneg, true);
                            auto y_mag_ub = product_justify::channel_bound_to_magnitude(*logger, yneg ? y_lb : y_ub, v2, enc.chan2, yneg);

                            auto glb = product_justify::grid_sum_lower_bound(*logger, reason, enc.grid, enc.chan1.mag, x_mag_lb, y_mag_lb);
                            auto gub =
                                product_justify::grid_sum_upper_bound(*logger, reason, enc.grid, enc.chan1.mag, enc.chan2.mag, x_mag_ub, y_mag_ub);
                            auto z_case_lower = zneg
                                ? product_justify::channel_grid_bound_to_result(*logger, reason, v3, enc.zchan, gub, true, false)
                                : product_justify::channel_grid_bound_to_result(*logger, reason, v3, enc.zchan, glb, false, true);
                            auto z_case_upper = zneg
                                ? product_justify::channel_grid_bound_to_result(*logger, reason, v3, enc.zchan, glb, true, true)
                                : product_justify::channel_grid_bound_to_result(*logger, reason, v3, enc.zchan, gub, false, false);

                            // clash whichever side violates z's actual range
                            optional<ProofLine> clash;
                            HalfReifyOnConjunctionOf clash_cases;
                            if (z_case_lower.rhs > zhi) {
                                PolBuilder b;
                                b.add(z_case_lower.line).add(z_ub.line).saturate();
                                clash = b.emit(*logger, ProofLevel::Temporary);
                                clash_cases = z_case_lower.cases;
                            }
                            else if (-z_case_upper.rhs < zlo) {
                                PolBuilder b;
                                b.add(z_case_upper.line).add(z_lb.line).saturate();
                                clash = b.emit(*logger, ProofLevel::Temporary);
                                clash_cases = z_case_upper.cases;
                            }
                            if (! clash) {
                                cerr << "FactorUpper: live case " << pattern << " does not refute\n";
                                exit(EXIT_FAILURE);
                            }
                            premises[pattern] = ConditionalBound{WPBSum{}, 1_i, clash_cases, *clash};
                        }
                        auto zero_refutations = vector<Literal>{};
                        if (ylo < 0_i && yhi >= 0_i)
                            zero_refutations.emplace_back(v2 != 0_i);
                        product_justify::conclude_by_sign_cases(*logger, reason, WPBSum{} + -1_i * v1 >= -q_hi, dims, premises, zero_refutations);
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (v1 <= q_hi) >= 1_i, ProofLevel::Temporary);
                        break;
                    }

                    case Fragment::SquareBounds: {
                        // z >= 0 is plain RUP for a square: the sign clauses
                        // degenerate (sgn_nn forces [x>=0], sgn_pp forces
                        // [x<1], eq0 then pins x = 0, sgn_x0 closes).
                        logger->emit_rup_proof_line(WPBSum{} + 1_i * (v3 >= 0_i) >= 1_i, ProofLevel::Temporary);

                        auto [xlo, xhi] = state.bounds(v1);
                        auto reason = ReasonLiterals{v1 >= xlo, v1 <= xhi};
                        auto [sq_lo, sq_hi] = square_bounds(xlo, xhi);
                        auto dims = vector<product_justify::SignCaseDimension>{{v1 >= 0_i, v1 < 0_i}};
                        vector<optional<ConditionalBound>> lower_premises(2, nullopt), upper_premises(2, nullopt);
                        for (unsigned pattern = 0; pattern < 2; ++pattern) {
                            bool xneg = pattern & 1u;
                            if (xneg ? xlo >= 0_i : xhi < 0_i)
                                continue;
                            auto ob_for_lb = product_justify::derive_operand_bound(*logger, reason, v1, ! xneg, xneg ? xhi : xlo);
                            auto ob_for_ub = product_justify::derive_operand_bound(*logger, reason, v1, xneg, xneg ? xlo : xhi);
                            auto lb1 = product_justify::channel_bound_to_magnitude(*logger, ob_for_lb, v1, enc.chan1, xneg);
                            auto lb2 = product_justify::channel_bound_to_magnitude(*logger, ob_for_lb, v1, enc.chan2, xneg);
                            auto ub1 = product_justify::channel_bound_to_magnitude(*logger, ob_for_ub, v1, enc.chan1, xneg);
                            auto ub2 = product_justify::channel_bound_to_magnitude(*logger, ob_for_ub, v1, enc.chan2, xneg);
                            auto glb = product_justify::grid_sum_lower_bound(*logger, reason, enc.grid, enc.chan1.mag, lb1, lb2);
                            auto gub = product_justify::grid_sum_upper_bound(*logger, reason, enc.grid, enc.chan1.mag, enc.chan2.mag, ub1, ub2);
                            lower_premises[pattern] = product_justify::channel_grid_bound_to_result(*logger, reason, v3, enc.zchan, glb, false, true);
                            upper_premises[pattern] =
                                product_justify::channel_grid_bound_to_result(*logger, reason, v3, enc.zchan, gub, false, false);
                        }
                        product_justify::conclude_by_sign_cases(*logger, reason, WPBSum{} + 1_i * v3 >= sq_lo, dims, lower_premises);
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (v3 >= sq_lo) >= 1_i, ProofLevel::Temporary);
                        product_justify::conclude_by_sign_cases(*logger, reason, WPBSum{} + -1_i * v3 >= -sq_hi, dims, upper_premises);
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (v3 <= sq_hi) >= 1_i, ProofLevel::Temporary);
                        break;
                    }
                    }
                },
                InitialiserPriority::Expensive);

            Triggers triggers;
            triggers.on_instantiated = {_v1, _v2, _v3};
            propagators.install(
                constraint_id(),
                [v1 = _v1, v2 = _v2, v3 = _v3](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    auto a = state.optional_single_value(v1), b = state.optional_single_value(v2), c = state.optional_single_value(v3);
                    if (a && b && c && *a * *b != *c)
                        inference.contradiction(logger, JustifyUsingRUP{}, ExplicitReason{ReasonLiterals{v1 == *a, v2 == *b, v3 == *c}});
                    return PropagatorState::Enable;
                },
                triggers);
        }

        [[nodiscard]] auto s_expr(const ProofModel * const) const -> SExpr override
        {
            return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("test_product_fragment")});
        }
    };
}

namespace
{
    auto run_fragment_test(
        bool proofs, Fragment fragment, const std::string & name, pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range) -> void
    {
        print(cerr, "product fragment {} over {} {} {}{}", name, v1_range, v2_range, v3_range, proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<int, int, int>> expected, actual;
        build_expected(expected, [](int a, int b, int c) { return a * b == c; }, v1_range, v2_range, v3_range);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second), "v1");
        auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second), "v2");
        auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second), "v3");
        p.post(ProductFragmentForTest{v1, v2, v3, fragment});

        auto proof_name = proofs ? make_optional("product_justify_test") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});
        check_results(proof_name, expected, actual);
    }
}

namespace
{
    auto run_square_fragment_test(bool proofs, Fragment fragment, const std::string & name, pair<int, int> x_range, pair<int, int> z_range) -> void
    {
        print(cerr, "square fragment {} over {} {}{}", name, x_range, z_range, proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<int, int>> expected, actual;
        build_expected(expected, [](int a, int c) { return a * a == c; }, x_range, z_range);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto v1 = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second), "v1");
        auto v3 = p.create_integer_variable(Integer(z_range.first), Integer(z_range.second), "v3");
        p.post(ProductFragmentForTest{v1, v1, v3, fragment});

        auto proof_name = proofs ? make_optional("product_justify_test") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{v1, v3});
        check_results(proof_name, expected, actual);
    }
}

auto main(int, char *[]) -> int
{
    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            break;

        run_fragment_test(proofs, Fragment::TrivialRup, "trivial rup", {2, 5}, {1, 3}, {2, 15});
        run_fragment_test(proofs, Fragment::TrivialRup, "trivial rup signed", {-3, 3}, {-2, 4}, {-12, 12});

        run_fragment_test(proofs, Fragment::ChannelBounds, "channel nonneg", {2, 5}, {1, 3}, {2, 15});
        run_fragment_test(proofs, Fragment::ChannelBounds, "channel neg", {-5, -2}, {-3, -1}, {2, 15});
        run_fragment_test(proofs, Fragment::ChannelBounds, "channel span", {-3, 3}, {-2, 4}, {-12, 12});

        run_fragment_test(proofs, Fragment::GridLower, "grid lower pos/pos", {2, 5}, {1, 3}, {2, 15});
        run_fragment_test(proofs, Fragment::GridLower, "grid lower zero lb", {0, 3}, {1, 3}, {0, 9});

        run_fragment_test(proofs, Fragment::GridUpper, "grid upper pos/pos", {2, 5}, {1, 3}, {2, 15});
        run_fragment_test(proofs, Fragment::GridUpper, "grid upper zero ub", {0, 3}, {0, 2}, {0, 6});

        run_fragment_test(proofs, Fragment::ProductBounds, "product bounds pos/pos", {2, 5}, {1, 3}, {1, 16});
        run_fragment_test(proofs, Fragment::ProductBounds, "product bounds neg/neg", {-5, -2}, {-3, -1}, {1, 16});
        run_fragment_test(proofs, Fragment::ProductBounds, "product bounds pos/neg", {2, 5}, {-3, -1}, {-16, 0});
        run_fragment_test(proofs, Fragment::ProductBounds, "product bounds span/span", {-3, 3}, {-2, 4}, {-13, 13});
        run_fragment_test(proofs, Fragment::ProductBounds, "product bounds span/pos", {-3, 3}, {1, 4}, {-13, 13});

        run_fragment_test(proofs, Fragment::FactorUpper, "factor upper y pos", {-6, 8}, {2, 3}, {7, 7});
        run_fragment_test(proofs, Fragment::FactorUpper, "factor upper y neg", {-8, 5}, {-3, -2}, {6, 12});
        run_fragment_test(proofs, Fragment::FactorUpper, "factor upper y span", {-4, 12}, {-2, 3}, {4, 9});

        run_square_fragment_test(proofs, Fragment::SquareBounds, "square span", {-3, 4}, {-2, 17});
        run_square_fragment_test(proofs, Fragment::SquareBounds, "square pos", {2, 5}, {0, 30});
        run_square_fragment_test(proofs, Fragment::SquareBounds, "square neg", {-5, -2}, {3, 26});
    }

    return EXIT_SUCCESS;
}
