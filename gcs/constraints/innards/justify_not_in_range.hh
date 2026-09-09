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
    // each of which is RUP by Theorem 2.9 of Matthew's thesis (contradictory
    // constraints on binary sums): its negation supplies a *lower* bound on one
    // operand against an *upper* bound on the other, across a row that is their
    // difference, which always unit propagates to contradiction. The lemmas
    // mention no range literal, so any literal sharing these endpoints can reuse
    // them.
    //
    // [other_lo, other_hi] are the bounds the range forces on `other` through the
    // equality; for a plain `pruned = other` they are [lo, hi].
    //
    // **The pairing is the hypothesis, and a sign-flipped link does not satisfy
    // it.** Against `pruned = -other` the row is a sum rather than a difference,
    // the negation supplies two bounds on the same side, and the configuration is
    // outside the theorem -- with a measured non-propagating instance, see the
    // Theorem 2.9 section of dev_docs/large-domains.md. Abs' negative branch is
    // that case and uses pol instead (abs/justify.cc); do not reach for this
    // helper with a mirrored pairing and expect it to hold.
    //
    // `other` must be a plain integer variable, equality-linked to `pruned` in the
    // proof model. Pass the same reason the caller hands to infer_not_in_range.
    auto justify_not_in_range_across_equality(ProofLogger & logger, const ReasonLiterals & reason, const SimpleIntegerVariableID & pruned, Integer lo,
        Integer hi, IntegerVariableID other, Integer other_lo, Integer other_hi) -> void;
}

#endif
