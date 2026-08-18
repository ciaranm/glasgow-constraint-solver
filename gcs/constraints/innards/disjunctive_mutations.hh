#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_DISJUNCTIVE_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_DISJUNCTIVE_MUTATIONS_HH

#include <variant>

/**
 * \file
 *
 * Deliberate corruptions of `Disjunctive`'s detectable-precedence and
 * presence-falsification proof steps, which exist so that a test can show the
 * honest derivation is tight to what it
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

        /// Emit no overload certificate at all, leaving the contradiction to
        /// the framework's wrapping RUP. The control for that rule: unlike
        /// presence falsification, an overload's reason context is *not*
        /// contradictory until the argument makes it so, which is why the
        /// route mutations below bite where that rule's could not.
        struct OverloadEmitNothing
        {
        };

        /// Leave the per-time at-most-ones out of the overload endgame, so
        /// nothing says the window can hold only one task at a time and the
        /// energies have no supply to exceed.
        struct SkipOverloadFold
        {
        };

        /// Leave the tasks' energies out of the overload endgame, so nothing
        /// says how much work the window must contain.
        struct SkipOverloadEnergy
        {
        };

        /// Conclude each pair's per-time at-most-one by bare `rup` rather than
        /// by the bridge pol. The step with no counterpart in Cumulative, and
        /// the one worth knowing propagation cannot make: getting from the
        /// pairwise encoding to a statement about a time point is arithmetic,
        /// not propagation.
        struct RupOverloadBridge
        {
        };

        /// Emit no edge-finding certificate at all, leaving the push to the
        /// framework's wrapping RUP. The control for that rule.
        struct EdgeFindingEmitNothing
        {
        };

        /// Leave the per-time at-most-ones out of edge-finding's endgame, so
        /// nothing says the window can hold only one task at a time.
        struct SkipEdgeFindingFold
        {
        };

        /// Leave one contained task's guarded energy row out, so the window is
        /// charged less work than the detection counted.
        struct DropContainedEnergy
        {
        };

        /// Push the bound one unit past where the energy argument reaches.
        /// **The signature test for this rule**: unlike the overload check,
        /// whose destination makes every route valid, edge-finding prunes, so
        /// corrupting the conclusion is what a mutation has to do. Corruptions
        /// that merely shorten the route verify happily once the reason context
        /// extended with the negated conclusion has gone contradictory.
        struct EdgeFindingOneTooFar
        {
        };

        /// Leave the *pushed* task's guarded energy row out, so nothing says
        /// the task has to be in the window at all and the contained tasks'
        /// energy alone has to overflow it --- which, the window having been
        /// checked not to be overloaded, it cannot.
        struct DropPushedEnergy
        {
        };

        // Deliberately absent: citing the pushed task's row at the *unclipped*
        // threshold, as if the window contained it. It was written, and it
        // verified. A row derived at a threshold the reason still entails is a
        // sound row --- a *stronger* one --- so a proof that cites it closes
        // just the same, and the mutation tests nothing. What it would have
        // been aimed at is the propagator firing on more energy than the row it
        // cites establishes, and `cumulative-proof-logging.md` records the same
        // conclusion: no mutation lane can catch that, so the propagator asks
        // `window_energy_bound` for exactly the guards the derivation will be
        // given instead, and that invariant is what has to be read rather than
        // tested.
    }

    using DisjunctiveProofMutation = std::variant<disjunctive_proof_mutation::None, disjunctive_proof_mutation::EmitNothing,
        disjunctive_proof_mutation::SkipRefutation, disjunctive_proof_mutation::SkipTargetFold, disjunctive_proof_mutation::LooseDetectionBound,
        disjunctive_proof_mutation::PushOneTooFar, disjunctive_proof_mutation::OverloadEmitNothing, disjunctive_proof_mutation::SkipOverloadFold,
        disjunctive_proof_mutation::SkipOverloadEnergy, disjunctive_proof_mutation::RupOverloadBridge,
        disjunctive_proof_mutation::EdgeFindingEmitNothing, disjunctive_proof_mutation::SkipEdgeFindingFold,
        disjunctive_proof_mutation::DropContainedEnergy, disjunctive_proof_mutation::EdgeFindingOneTooFar,
        disjunctive_proof_mutation::DropPushedEnergy>;

    /**
     * \brief Deliberate corruptions of the presence-falsification derivation,
     * for testing only. VeriPB must reject each of them.
     *
     * What can serve as a test here is narrower than for a bound push, and
     * worth understanding before adding to this list: presence falsification is
     * a *conflict-shaped* rule, whose content is "this task cannot be here at
     * all". Once the chain has cornered the task, the reason context extended
     * with "the task is present" is contradictory, and every RUP under it is
     * vacuously valid. A mutation that merely shortens the chain therefore
     * produces a shorter but still *sound* derivation, and VeriPB is right to
     * accept it. Corrupting the route is not a test; corrupt the destination.
     * `cumulative_mutations.hh` records the same finding, from the constraint
     * this rule is modelled on.
     *
     * So the two that bite are \ref disjunctive_presence_mutation::WrongTask,
     * which argues about a task nothing has cornered, and \ref
     * disjunctive_presence_mutation::ClaimOneTooFar, which draws the conclusion
     * where it is false. \ref disjunctive_presence_mutation::EmitNothing is the
     * control that says the chain is required at all.
     *
     * All but ClaimOneTooFar change nothing except the proof: the same
     * presences are falsified, the same solutions reported, and the OPB is
     * untouched. ClaimOneTooFar necessarily changes the inference, since making
     * the conclusion wrong is the whole point of it.
     *
     * \ingroup Innards
     */
    namespace disjunctive_presence_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Carry some other optional task's presence literal on the chain's
        /// deposits, so the derivation argues about a task that is not the one
        /// being falsified.
        struct WrongTask
        {
        };

        /// Fire on an instance where exactly one placement still fits, claiming
        /// the task is absent when it is not. The "bound + 1 must fail" check
        /// for this rule: it corrupts the conclusion rather than the route to
        /// it, which is what a margin of exactly one unit is there to expose.
        struct ClaimOneTooFar
        {
        };

        /// Emit no chain at all, leaving the inference to the framework's
        /// wrapping RUP. Not a corruption but a control: if VeriPB accepts
        /// this, the chain is decoration and no mutation of it can be caught.
        struct EmitNothing
        {
        };
    }

    using DisjunctivePresenceMutation = std::variant<disjunctive_presence_mutation::None, disjunctive_presence_mutation::WrongTask,
        disjunctive_presence_mutation::ClaimOneTooFar, disjunctive_presence_mutation::EmitNothing>;
}

#endif
