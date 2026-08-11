#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_DISJUNCTIVE_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_DISJUNCTIVE_MUTATIONS_HH

#include <variant>

/**
 * \file
 *
 * Deliberate corruptions of `Disjunctive`'s detectable-precedence proof steps,
 * which exist so that a test can show the honest derivation is tight to what it
 * claims. They live here, in the innards, rather than beside the constraint they
 * corrupt: a header a user of the library includes should not advertise a way to
 * make the solver emit deliberately wrong proofs. Same reason as
 * `cumulative_mutations.hh`, and issue #669.
 */

namespace gcs::innards
{
    /**
     * \brief Deliberate corruptions of the detectable-precedence derivation,
     * for testing only.
     *
     * A proof that verifies is necessary but not sufficient: if the honest
     * derivation has slack in it, a wrong one verifies too, and the rule's
     * reasoning is then not being checked by anything. Each of these breaks one
     * step of the emitted derivation in a way that must make VeriPB *reject* the
     * proof; a mutation that still verifies is a finding about the honest
     * derivation, not about the mutation.
     *
     * A detectable precedence is a bound *push*, so — unlike a conflict-shaped
     * rule, where the reason context is already contradictory and every later
     * RUP is vacuously valid — corrupting the route to the conclusion is a real
     * test here as well as corrupting the conclusion. The two halves of the
     * derivation are separately droppable, and each drop must be caught.
     *
     * All but \ref disjunctive_proof_mutation::PushOneTooFar change nothing but
     * the proof: the same bounds are pushed, the same solutions reported, and
     * the OPB is untouched. PushOneTooFar necessarily changes the inference,
     * since making the conclusion false is the whole point of it.
     *
     * \ingroup Innards
     */
    namespace disjunctive_proof_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Emit no pols at all, leaving the push to the framework's wrapping
        /// RUP. Not a corruption but a control: if VeriPB accepts this, the
        /// derivation is decoration and no mutation of it can be caught.
        struct EmitNothing
        {
        };

        /// Skip the pol that refutes the reverse precedence, so nothing rules
        /// out the successor finishing first and the separation clause never
        /// forces the surviving direction.
        struct SkipRefutation
        {
        };

        /// Skip the pol that folds the surviving precedence onto the target
        /// order literal, so the push has no route from "the predecessor
        /// finishes first" to a bound on the successor's start.
        struct SkipTargetFold
        {
        };

        /// Cite a running bound one unit weaker than the reason supports, so
        /// the refutation pol is one unit short of detecting the precedence.
        /// On a margin-of-one instance that is exactly the difference between
        /// a clause and a triviality.
        struct LooseDetectionBound
        {
        };

        /// Push the bound one unit past where the detected precedence puts it,
        /// which is false. The "bound + 1 must fail" check for this rule:
        /// it corrupts the conclusion rather than the route to it, which is
        /// what a margin of exactly one unit is there to expose.
        struct PushOneTooFar
        {
        };
    }

    using DisjunctiveProofMutation =
        std::variant<disjunctive_proof_mutation::None, disjunctive_proof_mutation::EmitNothing, disjunctive_proof_mutation::SkipRefutation,
            disjunctive_proof_mutation::SkipTargetFold, disjunctive_proof_mutation::LooseDetectionBound, disjunctive_proof_mutation::PushOneTooFar>;
}

#endif
