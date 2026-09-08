#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_JUSTIFY_HH

#include <gcs/innards/proofs/proof_logger.hh>

namespace gcs::innards
{
    // Hole removal: justifies v2 != val by case-splitting on v1's sign.
    // Used in the v1 -> v2 direction when both val and -val are absent
    // from dom(v1).
    auto justify_abs_hole(ProofLogger & logger, const ReasonLiterals & reason, IntegerVariableID v1, IntegerVariableID v2, Integer val) -> void;

    // The range form of the same removal: justifies `~[v2 in lo..hi]` from a
    // reason saying v1 holds nothing in [lo, hi] and nothing in [-hi, -lo].
    //
    // The per-value form gets away with two RUP lines because `v2 == val` pins
    // every bit of v2, which pins v1's through whichever half-reified row is
    // active. A range pins no bit, and the bounds it does give sit on *opposite
    // sides* of the row, so closing it means adding two PB bound constraints to
    // the row --- which unit propagation cannot do. (This is why the guarded
    // two-lemma RUP shape min_max.cc and element.cc use does not transfer here.
    // There the guard is falsified by the conclusion's own negation, and the
    // remaining slack arithmetic happens to line up; measured on Abs it misses
    // by one, see dev_docs/large-domains.md.)
    //
    // So each branch's two bounds are derived by `pol` instead, in the same
    // resolution shape as the consequence-bound helpers below: the model half,
    // plus the defining item of each atom whose arithmetic is used. That leaves
    // one clause per branch whose only free literal is the sign, and the two
    // signs being a literal and its negation, the conclusion follows by RUP.
    //
    // Four resolutions and two RUP lines per removed range, independent of its
    // width, which is the property that matters. Both variables must be plain:
    // a range literal on a view is not available (issue #882), and a constant
    // has no order-encoding atoms to resolve against. Width-1 ranges are left
    // to justify_abs_hole, which is what they canonicalise to anyway.
    auto justify_abs_hole_range(ProofLogger & logger, const ReasonLiterals & reason, const SimpleIntegerVariableID & v1,
        const SimpleIntegerVariableID & v2, Integer lo, Integer hi, ProofLine abs_nonneg_le, ProofLine abs_nonneg_ge, ProofLine abs_neg_le,
        ProofLine abs_neg_ge) -> void;

    // The mirrored direction: justifies `~[v1 in lo..hi]` where the caller's
    // reason says v2 holds nothing in abs([lo, hi]). Takes no ReasonLiterals: all
    // three of its lines are pol consequences of the model alone, so unlike the
    // image direction none of them has to be stated under the reason.
    //
    // Cheaper than the above, and the asymmetry is the interesting part. [lo, hi]
    // must lie wholly on one side of zero, which the caller arranges by splitting
    // at zero; the conclusion's own negation then decides v1's sign, so only the
    // active branch is needed and there is no case split left to close. Three
    // resolutions: the sign, and the two bounds it licenses.
    //
    // Same plain-variable requirement as above.
    auto justify_abs_preimage_range(ProofLogger & logger, const SimpleIntegerVariableID & v1, const SimpleIntegerVariableID & v2, Integer lo,
        Integer hi, ProofLine abs_nonneg_le, ProofLine abs_nonneg_ge, ProofLine abs_neg_le, ProofLine abs_neg_ge) -> void;

    // The bound proofs below share their resolution shape between the
    // prepare-time initialiser and the run-time propagator. The initialiser
    // calls them with empty ReasonLiterals (the operand bound RUPs from
    // the encoding's initial domain); the propagator passes its reason in
    // so the operand bound RUPs under that literal instead. In both cases
    // the helper short-circuits when v1 is constant -- the encoding's
    // relevant half is then unreified and plain RUP closes the inference
    // without an explicit pol step.

    // v2 >= 0. Initialiser-only: at run time v1 spanning zero already keeps
    // v2's lower bound at 0, and the entirely-positive/negative cases use
    // justify_abs_v2_lb below.
    auto justify_abs_v2_ge_zero(ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, ProofLine abs_nonneg_ge) -> void;

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
    auto justify_abs_v2_lb(ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, AbsLbSide side, Integer v2_lb, ProofLine abs_ge,
        const ReasonLiterals & reason) -> void;

    // v1 <= v2_ub.
    auto justify_abs_v1_le_v2_ub(ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, Integer v2_ub, ProofLine abs_nonneg_ge,
        const ReasonLiterals & reason) -> void;

    // v1 >= -v2_ub.
    auto justify_abs_v1_ge_neg_v2_ub(
        ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, Integer v2_ub, ProofLine abs_neg_ge, const ReasonLiterals & reason) -> void;

    // v2 <= big_m, where big_m = max(-v1_lb, v1_ub).
    auto justify_abs_v2_le_big_m(ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, Integer v1_lb, Integer v1_ub, Integer big_m,
        ProofLine abs_nonneg_le, ProofLine abs_neg_le, const ReasonLiterals & reason) -> void;
}

#endif
