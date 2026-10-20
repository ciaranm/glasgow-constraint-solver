#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_JUSTIFY_HH

#include <gcs/innards/proofs/proof_logger.hh>

namespace gcs::innards
{
    // Range hole removal: justifies `~[v2 in lo..hi]` from a reason saying v1
    // holds nothing in [lo, hi] and nothing in [-hi, -lo].
    //
    // The per-value form (in abs.cc) is a single `cases` line on v1's sign with
    // no lemmas, because `v2 == val` pins every bit of v2, which pins v1's
    // through whichever half-reified row the branch makes active. A range pins
    // no bit, so it needs the bound lemmas min_max.cc and
    // element.cc use -- and those are Theorem 2.9, which wants a lower bound on
    // one operand against an upper bound on the other across their *difference*.
    // This constraint's negative branch links v2 to -v1, so its row is a sum and
    // the negation gives two bounds on the same side: outside the theorem, with a
    // measured non-propagating instance. The non-negative branch *is* a
    // difference and would take the RUP form; pol is used for both so there is
    // one shape to read. See the Theorem 2.9 section of
    // dev_docs/large-domains.md.
    //
    // So each branch's two bounds are derived by `pol` instead, in the same
    // resolution shape as the consequence-bound helpers below: the model half,
    // plus the defining item of each atom whose arithmetic is used. That leaves
    // one clause per branch whose only free literal is the sign, and the two
    // signs being a literal and its negation, the conclusion follows by RUP.
    //
    // Four resolutions and two RUP lines per removed range, independent of its
    // width, which is the property that matters. Neither variable may be a
    // constant, which pins every bit and so has no order-encoding atom for
    // these resolutions to name; a view is fine, because each atom is taken
    // over whichever encoded variable its operand resolves to, and since #904
    // a registered view has one of its own (#931). Width-1 ranges are left to
    // the per-value form, which is what they canonicalise to anyway.
    auto justify_abs_hole_range(ProofLogger & logger, const ReasonLiterals & reason, const IntegerVariableID & v1, const IntegerVariableID & v2,
        Integer lo, Integer hi, ProofLine abs_nonneg_le, ProofLine abs_nonneg_ge, ProofLine abs_neg_le, ProofLine abs_neg_ge) -> void;

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
    // Same non-constant requirement as above, and for the same reason -- plus
    // v1's two sign atoms, which this direction resolves against and the other
    // does not.
    auto justify_abs_preimage_range(ProofLogger & logger, const IntegerVariableID & v1, const IntegerVariableID & v2, Integer lo, Integer hi,
        ProofLine abs_nonneg_le, ProofLine abs_nonneg_ge, ProofLine abs_neg_le, ProofLine abs_neg_ge) -> void;

    // v2 <= big_m, where big_m = max(-v1_lb, v1_ub). The one bound rule left
    // with a helper. The other bounds are plain RUP or a sign split, because
    // their crossing over the active half is Theorem 2.9. This one needs both
    // branches, and the negative branch carries v1's lower bound into an upper
    // bound on v2 across v2 + v1 <= 0, which is outside the theorem, with
    // non-propagating instances from v1 in [-33, 32] up. So it is one
    // resolution per sign, and the final RUP combines them. Shared by the
    // initialiser, which passes empty ReasonLiterals so the operand bounds RUP
    // from the initial domains, and the propagator, which passes its reason.
    // It short-circuits when v1 is constant: the relevant half is then
    // unreified and plain RUP closes the inference.
    auto justify_abs_v2_le_big_m(ProofLogger & logger, IntegerVariableID v1, IntegerVariableID v2, Integer v1_lb, Integer v1_ub, Integer big_m,
        ProofLine abs_nonneg_le, ProofLine abs_neg_le, const ReasonLiterals & reason) -> void;
}

#endif
