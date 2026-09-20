#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_PLUS_MINUS_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_PLUS_MINUS_MUTATIONS_HH

#include <variant>

/**
 * \file
 *
 * Deliberate corruptions of the Plus/Minus consistency::GAC arm's proof steps,
 * which exist so that a test can show its derivation is tight to what it claims
 * (issue #192). They live here, in the innards, for the same reason
 * EqualsProofMutation does: a header a user of the library includes should not
 * advertise a way to make the solver emit deliberately wrong proofs.
 *
 * Each of these changes the proof and nothing else: the same inferences are
 * made, the same solutions reported, and the OPB is untouched.
 *
 * The arm is shared by Plus and Minus, and only Plus takes the knob: the two
 * differ in one coefficient, which the honest proofs already exercise, and the
 * question the lanes ask is about the shape of the argument, not its signs.
 */

namespace gcs::innards
{
    /**
     * \brief Deliberate corruptions of the Plus/Minus GAC arm's derivation, for
     * testing only. VeriPB must reject each of them.
     *
     * A mutation that still verifies is a finding about the honest derivation,
     * not about the mutation.
     *
     * \ingroup Innards
     */
    namespace plus_minus_proof_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Emit no bound lemmas before a range conclusion, so it is claimed to be
        /// RUP against the sum line on its own. This tests the design claim the
        /// whole derivation rests on: RUP cannot make a linear deduction across a
        /// three-variable sum. If VeriPB accepts this, the lemmas are decoration.
        struct OmitLemmas
        {
        };

        /// Emit the lemmas for the windows past the other variable's bounds, but
        /// not the pair for each window inside one of its holes, so the walk has
        /// to cross the holes unaided.
        struct OmitHoleLemmas
        {
        };

        /// Leave the holes of the variable whose holes hold the windows out of
        /// the reason, so the walk is claimed to step over them from the bounds
        /// alone. Only a corruption where a hole arises under a search decision:
        /// a root hole is a fact the checker already has, whatever the reason
        /// says (see the mutation testing notes in dev_docs/constraints.md).
        struct DropWindowHoles
        {
        };
    }

    /**
     * \brief One of the plus_minus_proof_mutation corruptions, or None.
     *
     * \ingroup Innards
     */
    using PlusMinusProofMutation = std::variant<plus_minus_proof_mutation::None, plus_minus_proof_mutation::OmitLemmas,
        plus_minus_proof_mutation::OmitHoleLemmas, plus_minus_proof_mutation::DropWindowHoles>;
}

#endif
