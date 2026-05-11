#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_JUSTIFY_HH

#include <gcs/innards/proofs/proof_logger.hh>

namespace gcs::innards
{
    // Hole removal: justifies v2 != val by case-splitting on v1's sign.
    // Used in the v1 -> v2 direction when both val and -val are absent
    // from dom(v1).
    auto justify_abs_hole(
        ProofLogger & logger,
        const ReasonFunction & reason,
        IntegerVariableID v1,
        IntegerVariableID v2,
        Integer val) -> void;

    // The bound proofs below share their resolution shape between the
    // prepare-time initialiser and the run-time propagator. The initialiser
    // calls them with an empty ReasonFunction (the operand bound RUPs from
    // the encoding's initial domain); the propagator passes its reason in
    // so the operand bound RUPs under that literal instead. In both cases
    // the helper short-circuits when v1 is constant -- the encoding's
    // relevant half is then unreified and plain RUP closes the inference
    // without an explicit pol step.

    // v2 >= 0. Initialiser-only: at run time v1 spanning zero already keeps
    // v2's lower bound at 0, and the entirely-positive/negative cases use
    // justify_abs_v2_lb below.
    auto justify_abs_v2_ge_zero(
        ProofLogger & logger,
        IntegerVariableID v1,
        IntegerVariableID v2,
        ProofLine abs_nonneg_ge) -> void;

    // Side picks which half-reified piece drives the proof:
    //   Nonneg: dom(v1) sits at or above v1_bound >= 1; abs_ge is the
    //           encoding's "Abs non-negative" >= half.
    //   Nonpos: dom(v1) sits at or below v1_bound <= -1; abs_ge is the
    //           encoding's "Abs negative" >= half.
    enum struct AbsLbSide
    {
        Nonneg,
        Nonpos
    };

    // v2 >= v2_lb. Propagator-only -- the initialiser cannot move this
    // bound above 0 since at search start v1 spans zero whenever v2's
    // image-min is positive.
    auto justify_abs_v2_lb(
        ProofLogger & logger,
        IntegerVariableID v1,
        IntegerVariableID v2,
        AbsLbSide side,
        Integer v2_lb,
        ProofLine abs_ge,
        const ReasonFunction & reason) -> void;

    // v1 <= v2_ub.
    auto justify_abs_v1_le_v2_ub(
        ProofLogger & logger,
        IntegerVariableID v1,
        IntegerVariableID v2,
        Integer v2_ub,
        ProofLine abs_nonneg_ge,
        const ReasonFunction & reason) -> void;

    // v1 >= -v2_ub.
    auto justify_abs_v1_ge_neg_v2_ub(
        ProofLogger & logger,
        IntegerVariableID v1,
        IntegerVariableID v2,
        Integer v2_ub,
        ProofLine abs_neg_ge,
        const ReasonFunction & reason) -> void;

    // v2 <= big_m, where big_m = max(-v1_lb, v1_ub).
    auto justify_abs_v2_le_big_m(
        ProofLogger & logger,
        IntegerVariableID v1,
        IntegerVariableID v2,
        Integer v1_lb,
        Integer v1_ub,
        Integer big_m,
        ProofLine abs_nonneg_le,
        ProofLine abs_neg_le,
        const ReasonFunction & reason) -> void;
}

#endif
