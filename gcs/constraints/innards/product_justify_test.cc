#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/innards/product_encoding.hh>
#include <gcs/constraints/innards/product_justify.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
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
    }

    return EXIT_SUCCESS;
}
