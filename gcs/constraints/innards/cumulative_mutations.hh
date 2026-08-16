#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CUMULATIVE_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CUMULATIVE_MUTATIONS_HH

#include <variant>

/**
 * \file
 *
 * Deliberate corruptions of `Cumulative`'s proof steps, which exist so that a
 * test can show the honest derivation is tight to what it claims. They live
 * here, in the innards, rather than beside the constraint they corrupt: a
 * header a user of the library includes should not advertise a way to make the
 * solver emit deliberately wrong proofs. Issue #669, and the same reason
 * SubsetSumMutation and Am1FromPairsMutation were always here.
 *
 * Compiling them out of release builds was considered and rejected. The hooks
 * are not only `if` bodies --- the flags are lambda captures in the derived
 * constraint recipes and members that `clone()` copies --- so a build without
 * them would ship a different closure from the one the tests exercised, and for
 * proof logging, whose failure mode is "verifies fine but says something other
 * than what it claimed", that is the worst place to put a configuration-
 * dependent divergence. The mutation tests are also the only tests here that
 * can fail for the right reason, since solutions matching brute force and
 * veripb verifying both pass just as well when the derivation did nothing.
 */

namespace gcs::innards
{
    /**
     * \brief Deliberate corruptions of the overload check's derivation, for
     * testing only.
     *
     * A proof that verifies is necessary but not sufficient: if the honest
     * derivation has slack in it, a wrong one verifies too, and the rule's
     * arithmetic is then not being checked by anything. Each of these breaks
     * one step of the emitted derivation in a way that must make VeriPB
     * *reject* the proof; a mutation that still verifies is a finding about the
     * honest derivation, not about the mutation.
     *
     * These change nothing but the proof: the same conflicts are found, the
     * same solutions reported, and the OPB is untouched.
     *
     * \ingroup Innards
     */
    namespace cumulative_proof_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Claim one more unit of activity than the window-energy lemma
        /// derived, for the first task in the window.
        struct OverstateWindowEnergy
        {
        };

        /// Leave the last time point's capacity line out of the conflict's
        /// pol, so the window appears to supply one time point less than the
        /// energy argument was told.
        struct OmitCapacityLine
        {
        };

        /// Derive each task's window energy over a window one time point
        /// short, which is honest but weaker than the conflict needs.
        struct ShrinkLemmaWindow
        {
        };

        /// Edge-finding: leave one of the window's contained tasks out of the
        /// pol, so the energy claimed falls short of what the push needs.
        struct DropContainedTask
        {
        };

        /// Edge-finding: push the bound one further than the energy supports.
        struct PushOneTooFar
        {
        };

        /// TTEF: leave the first mandatory (task, time) pin out of the pol, so
        /// the profile load the push relied on is one unit short.
        struct DropProfilePin
        {
        };

        /// TTEF: leave *every* mandatory (task, time) pin out of the pol, so
        /// the push is left resting on edge-finding's energy alone.
        struct DropProfilePins
        {
        };

        /// (KAOC): claim one unit better than the largest total the heights at
        /// a time point can actually reach. This is the mutation the knapsack
        /// rule exists for --- it corrupts the *conclusion* of the integrality
        /// argument rather than the route to it, so a derivation with any slack
        /// in it verifies anyway and the rule is then resting on nothing.
        struct ClaimOneBetterAvailability
        {
        };

        /// (KAOC): apply the knapsack cap at one fewer time point than the
        /// conflict needs, which is honest but leaves the window supplying more
        /// than the comparison was told.
        struct StrengthenOneFewer
        {
        };

    }

    using CumulativeProofMutation = std::variant<cumulative_proof_mutation::None, cumulative_proof_mutation::OverstateWindowEnergy,
        cumulative_proof_mutation::OmitCapacityLine, cumulative_proof_mutation::ShrinkLemmaWindow, cumulative_proof_mutation::DropContainedTask,
        cumulative_proof_mutation::PushOneTooFar, cumulative_proof_mutation::DropProfilePin, cumulative_proof_mutation::DropProfilePins,
        cumulative_proof_mutation::ClaimOneBetterAvailability, cumulative_proof_mutation::StrengthenOneFewer>;

    /**
     * \brief Deliberate corruptions of the presence-falsification derivation,
     * for testing only. VeriPB must reject each of them.
     *
     * A proof that verifies is necessary but not sufficient, so something has
     * to check that the derivation is doing work. What that something can be is
     * narrower here than for a bound push, and worth understanding before
     * adding to this list: presence falsification is a *conflict-shaped* rule,
     * whose content is "this task cannot be here at all". Once the chain has
     * narrowed the start domain far enough, the reason context extended with
     * "the task is present" is contradictory, and every RUP under it is
     * vacuously valid. A mutation that merely shortens the chain therefore
     * produces a shorter but still *sound* derivation, and VeriPB is right to
     * accept it. Corrupting the route is not a test; corrupt the destination.
     *
     * So the two that bite are \ref cumulative_presence_mutation::WrongTask,
     * which argues about a task nothing has cornered, and \ref
     * cumulative_presence_mutation::ClaimOneTooFar, which draws the conclusion
     * where it is false. \ref cumulative_presence_mutation::EmitNothing is the
     * control that says the chain is required at all.
     *
     * All but ClaimOneTooFar change nothing except the proof: the same
     * presences are falsified, the same solutions reported, and the OPB is
     * untouched. ClaimOneTooFar necessarily changes the inference, since making
     * the conclusion wrong is the whole point of it.
     *
     * \ingroup Innards
     */
    namespace cumulative_presence_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Carry some other optional task's presence literal through the chain,
        /// so the derivation argues about a task that is not the one being
        /// falsified.
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

    using CumulativePresenceMutation = std::variant<cumulative_presence_mutation::None, cumulative_presence_mutation::WrongTask,
        cumulative_presence_mutation::ClaimOneTooFar, cumulative_presence_mutation::EmitNothing>;
}

#endif
