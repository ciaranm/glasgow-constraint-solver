#include <gcs/constraints/abs.hh>
#include <gcs/constraints/abs/justify.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <optional>
#include <sstream>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::holds_alternative;
using std::max;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

namespace
{
    // PB resolution: sum the operand proof lines and saturate, eliminating
    // any literals whose coefficients cancel. Emitted via VeriPB's polish-
    // notation rule, hence "pol ... + s" in the wire format.
    auto emit_resolution(ProofLogger * const logger, ProofLine a, ProofLine b) -> void
    {
        stringstream pol;
        pol << "pol " << a << " " << b << " + s ;";
        logger->emit_proof_line(pol.str(), ProofLevel::Temporary);
    }

    auto emit_resolution(ProofLogger * const logger, ProofLine a, ProofLine b, ProofLine c) -> void
    {
        stringstream pol;
        pol << "pol " << a << " " << b << " + " << c << " + s ;";
        logger->emit_proof_line(pol.str(), ProofLevel::Temporary);
    }
}

Abs::Abs(const IntegerVariableID v1, const IntegerVariableID v2) :
    _v1(v1),
    _v2(v2)
{
}

auto Abs::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Abs>(_v1, _v2);
}

auto Abs::install(Propagators & propagators, State &, ProofModel * const optional_model) && -> void
{
    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Abs::define_proof_model(ProofModel & model) -> void
{
    _abs_nonneg_lines = model.add_constraint("Abs", "non-negative", WPBSum{} + 1_i * _v2 + -1_i * _v1 == 0_i, HalfReifyOnConjunctionOf{_v1 >= 0_i});
    _abs_neg_lines = model.add_constraint("Abs", "negative", WPBSum{} + 1_i * _v2 + 1_i * _v1 == 0_i, HalfReifyOnConjunctionOf{_v1 < 0_i});
}

auto Abs::install_propagators(Propagators & propagators) -> void
{
    // All four consequence bounds live in a single SimpleDefinition-priority
    // initialiser. The OPB encoding stays free of "Abs" labels for inferences
    // that aren't definitional; each bound's proof is assembled at search-init
    // time as PB resolution steps over the encoding's two half-reified halves
    // and the relevant `v_ge_X` flag definitions.
    //
    // VeriPB's RUP alone cannot derive any of these bounds for non-constant
    // v1, because it can't case-split on `v1 >= 0 \/ v1 < 0`. Each proof
    // callback supplies the case split explicitly: resolve a constraint that
    // holds under `v1 >= 0` with one that holds under `v1 < 0`, leaving the
    // flag literal the bound is about. The final RUP then closes the
    // inference. When v1 IS constant the encoding's relevant half is
    // unreified, so the proof callback emits nothing and plain RUP suffices.
    // When v2 is constant we bail out entirely — the propagator will discover
    // any UNSAT via per-value pruning.
    propagators.install_initialiser(
        [v1 = _v1, v2 = _v2,
            abs_nonneg_le = _abs_nonneg_lines.first,
            abs_nonneg_ge = _abs_nonneg_lines.second,
            abs_neg_le = _abs_neg_lines.first,
            abs_neg_ge = _abs_neg_lines.second](
            State & state, auto & inference, ProofLogger * const logger) -> void {
            if (holds_alternative<ConstantIntegerVariableID>(v2))
                return;

            auto v1_is_constant = holds_alternative<ConstantIntegerVariableID>(v1);

            // Bound 1: v2 >= 0. One resolution suffices — the v1 < 0 branch
            // (v2 = -v1 > 0) is short enough for VeriPB to chase through the
            // encoding once the v1 >= 0 branch is in the database.
            //   resolve(v1_ge0 part 1, Abs non-negative ≥ half, v2 < 0 part 2)
            //   → v2_ge0 ∨ ~v1_ge0.
            inference.infer(logger, v2 >= 0_i,
                JustifyExplicitlyThenRUP{
                    [logger, v1, v2, v1_is_constant, abs_nonneg_ge](const ReasonFunction &) -> void {
                        if (v1_is_constant)
                            return;
                        auto & ids = logger->names_and_ids_tracker();
                        auto v1_ge0 = std::get<ProofLine>(ids.need_pol_item_defining_literal(v1 >= 0_i));
                        auto v2_lt0 = std::get<ProofLine>(ids.need_pol_item_defining_literal(v2 < 0_i));
                        emit_resolution(logger, v1_ge0, *abs_nonneg_ge, v2_lt0);
                    }},
                ReasonFunction{});

            auto v2_ub = state.upper_bound(v2);

            // Bound 2: v1 <= ub(v2). Both case-split halves explicit (wider /
            // asymmetric domains stretch VeriPB's bit-level RUP). Skip if
            // ub(v2) < 0 — the v1_ge_(ub(v2)+1) flag would collide with
            // v1_ge0 / become vacuous; the propagator detects UNSAT directly.
            //   v1 >= 0: resolve(Abs nonneg ≥, v2 ≤ ub(v2), v1_ge_(ub(v2)+1) part 1)
            //            → ~v1_ge_(ub(v2)+1) ∨ ~v1_ge0.
            //   v1 < 0 : resolve(v1_ge_(ub(v2)+1) part 1, v1_ge0 part 2)
            //            → ~v1_ge_(ub(v2)+1) ∨ v1_ge0. (Trivial.)
            if (v2_ub >= 0_i) {
                inference.infer(logger, v1 < v2_ub + 1_i,
                    JustifyExplicitlyThenRUP{
                        [logger, v1, v2, v2_ub, v1_is_constant, abs_nonneg_ge](const ReasonFunction &) -> void {
                            if (v1_is_constant)
                                return;
                            auto & ids = logger->names_and_ids_tracker();
                            auto v1_ge_bound_plus_1 = std::get<ProofLine>(
                                ids.need_pol_item_defining_literal(v1 >= v2_ub + 1_i));
                            auto v2_upper = logger->emit_rup_proof_line(
                                WPBSum{} + 1_i * v2 <= v2_ub, ProofLevel::Temporary);
                            emit_resolution(logger, *abs_nonneg_ge, v2_upper, v1_ge_bound_plus_1);

                            auto v1_lt0 = std::get<ProofLine>(ids.need_pol_item_defining_literal(v1 < 0_i));
                            emit_resolution(logger, v1_ge_bound_plus_1, v1_lt0);
                        }},
                    ReasonFunction{});
            }

            // Bound 3: v1 >= -ub(v2). Mirror of bound 2 on the "Abs negative"
            // side. Skip if ub(v2) <= 0 (same flag-collision concern).
            //   v1 < 0 : resolve(Abs neg ≥, v2 ≤ ub(v2), v1_ge_(-ub(v2)) part 2)
            //            → v1_ge_(-ub(v2)) ∨ v1_ge0.
            //   v1 >= 0: resolve(v1_ge0 part 1, v1_ge_(-ub(v2)) part 2)
            //            → v1_ge_(-ub(v2)) ∨ ~v1_ge0. (Trivial.)
            if (v2_ub > 0_i) {
                inference.infer(logger, v1 >= -v2_ub,
                    JustifyExplicitlyThenRUP{
                        [logger, v1, v2, v2_ub, v1_is_constant, abs_neg_ge](const ReasonFunction &) -> void {
                            if (v1_is_constant)
                                return;
                            auto & ids = logger->names_and_ids_tracker();
                            auto v1_lt_neg_bound = std::get<ProofLine>(
                                ids.need_pol_item_defining_literal(v1 < -v2_ub));
                            auto v2_upper = logger->emit_rup_proof_line(
                                WPBSum{} + 1_i * v2 <= v2_ub, ProofLevel::Temporary);
                            emit_resolution(logger, *abs_neg_ge, v2_upper, v1_lt_neg_bound);

                            auto v1_ge0 = std::get<ProofLine>(ids.need_pol_item_defining_literal(v1 >= 0_i));
                            emit_resolution(logger, v1_ge0, v1_lt_neg_bound);
                        }},
                    ReasonFunction{});
            }

            // Bound 4: v2 <= max(ub(v1), -lb(v1)) = M. Mirror of bound 1 on
            // the "<=" side, needing both case-split halves explicit.
            //   v1 >= 0: resolve(Abs nonneg ≤, v1 ≤ ub(v1), v2_ge_(M+1) part 1)
            //            → ~v2_ge_(M+1) ∨ ~v1_ge0.
            //   v1 < 0 : resolve(Abs neg ≤, -v1 ≤ -lb(v1), v2_ge_(M+1) part 1)
            //            → ~v2_ge_(M+1) ∨ v1_ge0.
            auto [v1_lb, v1_ub] = state.bounds(v1);
            auto bound4 = max(v1_ub, -v1_lb);
            inference.infer(logger, v2 < bound4 + 1_i,
                JustifyExplicitlyThenRUP{
                    [logger, v1, v2, v1_lb, v1_ub, bound4, v1_is_constant, abs_nonneg_le, abs_neg_le](
                        const ReasonFunction &) -> void {
                        if (v1_is_constant)
                            return;
                        auto & ids = logger->names_and_ids_tracker();
                        auto v2_ge_M_plus_1 = std::get<ProofLine>(
                            ids.need_pol_item_defining_literal(v2 >= bound4 + 1_i));

                        auto v1_upper = logger->emit_rup_proof_line(
                            WPBSum{} + 1_i * v1 <= v1_ub, ProofLevel::Temporary);
                        emit_resolution(logger, *abs_nonneg_le, v1_upper, v2_ge_M_plus_1);

                        auto v1_lower = logger->emit_rup_proof_line(
                            WPBSum{} + -1_i * v1 <= -v1_lb, ProofLevel::Temporary);
                        emit_resolution(logger, *abs_neg_le, v1_lower, v2_ge_M_plus_1);
                    }},
                ReasonFunction{});
        },
        InitialiserPriority::SimpleDefinition);

    // _v2 = abs(_v1)
    Triggers triggers{.on_change = {_v1, _v2}};
    propagators.install([v1 = _v1, v2 = _v2](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        // remove from v1 any value whose absolute value isn't in v2's domain.
        for (const auto & val : state.each_value_mutable(v1))
            if (! state.in_domain(v2, abs(val))) {
                inference.infer_not_equal(logger, v1, val, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{v2 != abs(val)}; }});
            }

        // now remove from v2 any value whose +/-value isn't in v1's domain.
        for (const auto & val : state.each_value_mutable(v2)) {
            if (! state.in_domain(v1, val) && ! state.in_domain(v1, -val) && state.in_domain(v2, val)) {
                auto just = [v1, v2, val, logger](const ReasonFunction & reason) {
                    justify_abs_hole(*logger, reason, v1, v2, val);
                };
                inference.infer_not_equal(logger, v2, val, JustifyExplicitlyThenRUP{just}, ReasonFunction{[=]() { return Reason{{v1 != val, v1 != -val}}; }});
            }
        }

        return PropagatorState::Enable;
    },
        triggers);
}

auto Abs::s_exprify(const innards::ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} abs", _name);
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_v1));
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_v2));

    return s.str();
}
