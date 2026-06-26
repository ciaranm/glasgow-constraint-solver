#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_JUSTIFY_NOT_IN_RANGE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_JUSTIFY_NOT_IN_RANGE_HH

#include <gcs/innards/proofs/proof_logger.hh>

namespace gcs::innards
{
    // Make a `~[pruned in lo..hi]` conclusion derivable across an equality between
    // `pruned` and `other`. A range literal asserts only order atoms, never bits,
    // so on its own the conclusion cannot cross the bit-sum equality; this emits
    // the two ge-layer bound lemmas
    //
    //     pruned >= lo          ->  other >= other_lo
    //     other >= other_hi + 1 ->  pruned >= hi + 1
    //
    // each of which is RUP, because its negation supplies a pair of opposing
    // bounds that contradict the equality at the bit level. The lemmas mention no
    // range literal, so any literal sharing these endpoints can reuse them.
    //
    // [other_lo, other_hi] are the bounds the range forces on `other` through the
    // equality; for a plain `pruned = other` they are [lo, hi]. The pairing
    // assumes a same-sign link: a sign-flipped link (such as Abs) needs the
    // mirrored pairing. `other` must be a plain integer variable, equality-linked
    // to `pruned` in the proof model. Pass the same reason the caller hands to
    // infer_not_in_range.
    auto justify_not_in_range_across_equality(ProofLogger & logger, const ReasonLiterals & reason, const SimpleIntegerVariableID & pruned, Integer lo,
        Integer hi, IntegerVariableID other, Integer other_lo, Integer other_hi) -> void;
}

#endif
