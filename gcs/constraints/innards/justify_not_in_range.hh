#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_JUSTIFY_NOT_IN_RANGE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_JUSTIFY_NOT_IN_RANGE_HH

#include <gcs/innards/proofs/proof_logger.hh>

namespace gcs::innards
{
    // Bridge a range ("in") inference across an equality-type link, so that a
    // single ~[pruned in lo..hi] conclusion becomes RUP where per-line RUP alone
    // cannot reach it.
    //
    // The range flag [pruned in lo..hi] asserts only pruned's *order* atoms
    // (pruned >= lo and not pruned >= hi+1). With lo < hi it never pins pruned's
    // bits (McIlree thesis Theorem 2.8 fires only for a single value), so the flag
    // cannot cross a bit-sum equality by unit propagation: ~[pruned in lo..hi] is
    // not RUP on its own. This helper supplies the missing case-split. It emits the
    // two ge-layer bound-lemmas
    //
    //     pruned >= lo          ->  other >= other_lo
    //     other >= other_hi + 1 ->  pruned >= hi + 1
    //
    // each of which *is* RUP: its negation hands unit propagation a pair of opposing
    // bounds which, together with the equality linking pruned and other already in
    // the model, is the contradictory-binary-sums configuration of Theorem 2.9. The
    // caller then concludes ~[pruned in lo..hi] by RUP: the flag's reification
    // supplies pruned's two cuts, the first lemma carries the lower bound across,
    // the reason walks it up past the excluded interval, and the second lemma
    // carries it back to contradict the flag's upper cut. This is Justification
    // Procedure 3.2 (Comparison) materialising each bound across the equality;
    // justify_abs_hole is the per-value sign-split form of the same idea.
    //
    // The lemmas mention no flag, so they are reusable by any literal sharing these
    // endpoints, and they are exactly the cross-variable Inv1 link at the boundary
    // values in play, materialised locally per inference (the corrected form of
    // what the superseded analysis believed had to be a per-equality global
    // covering).
    //
    // [other_lo, other_hi] are the bounds the flag forces on `other` through the
    // link: for a plain equality pruned = other they are [lo, hi]. NOTE: unlike the
    // earlier flag-conditioned form, this pairing is orientation-sensitive — it
    // assumes a same-sign link (all current callers). A sign-flipped link (Abs,
    // pruned = -other) needs the mirrored pairing (pruned >= lo -> other <
    // other_hi + 1, and other >= other_lo wired to the upper cut). The result is
    // width-independent (two lemmas regardless of hi - lo). `other` must be
    // order-encoded (a plain integer variable) and equality-linked to `pruned` in
    // the proof model. Pass the same reason the caller hands to
    // infer_not_in_range. See dev_docs/range_literals_spec.md.
    auto justify_not_in_range_across_equality(
        ProofLogger & logger,
        const ReasonFunction & reason,
        const SimpleIntegerVariableID & pruned,
        Integer lo,
        Integer hi,
        IntegerVariableID other,
        Integer other_lo,
        Integer other_hi) -> void;
}

#endif
