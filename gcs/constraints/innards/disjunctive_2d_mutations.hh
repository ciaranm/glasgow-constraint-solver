#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_DISJUNCTIVE_2D_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_DISJUNCTIVE_2D_MUTATIONS_HH

#include <variant>

/**
 * \file
 *
 * Deliberate corruptions of `Disjunctive2D`'s cumulative-relaxation
 * certificate, which exist so that a test can show the honest derivation is
 * tight to what it claims. They live here, in the innards, rather than beside
 * the constraint they corrupt: a header a user of the library includes should
 * not advertise a way to make the solver emit deliberately wrong proofs. Same
 * reason as `disjunctive_mutations.hh` and `cumulative_mutations.hh`, and issue
 * #669.
 */

namespace gcs::innards
{
    /**
     * \brief Deliberate corruptions of the cumulative relaxation's derivation,
     * for testing only.
     *
     * A proof that verifies is necessary but not sufficient: if the honest
     * derivation has slack in it, a wrong one verifies too. Each of these
     * breaks one step in a way that must make VeriPB *reject* the proof; one
     * that still verifies is a finding about the honest derivation rather than
     * about the mutation.
     *
     * None of them changes the inference: the same bounds are pushed and the
     * same solutions reported, so a lane running one of these is asking about
     * the proof alone.
     *
     * \ingroup Innards
     */
    namespace disjunctive_2d_proof_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Emit no certificate at all, leaving the inference to the framework's
        /// wrapping RUP. Not a corruption but a control: if VeriPB accepts
        /// this, the whole derivation is decoration and no mutation of it could
        /// be caught.
        struct EmitNothing
        {
        };

        /// Refute only one of a pair's two time-axis disjuncts. What is left of
        /// their separation clause is then not a separation --- one of the
        /// rectangles may still pass the other on the time axis --- so the
        /// comparator network is being told something the model does not say.
        struct SkipOneRefutation
        {
        };

        /// Leave a pair's derived clause carrying only its own share of the
        /// guard, rather than weakening it up to the whole. The clause is still
        /// true; what goes is the network's ability to cancel a guard literal
        /// that no half of a case split carried, which is the discipline
        /// assume_with_guarded_separations imposes.
        struct SkipGuardWeakening
        {
        };

        /// Leave the non-strict zero-size escapes unpinned, carrying them in
        /// the guard alone. The closing RUP then has to reach `~escape` from
        /// `size >= 1` by bit arithmetic, which gets there for *one* escape and
        /// no more --- the network's final row can force a single unassigned
        /// flag, not two. So this one needs a fixture with two of them, which
        /// is why its lane does not run on the same instance as the others.
        struct SkipEscapePins
        {
        };

        /// The relaxation overload check: leave the window energies out of
        /// the sum, so the capacity rows have nothing to contradict.
        struct OverloadSkipEnergy
        {
        };

        /// The relaxation overload check: leave one time point's capacity row
        /// out of the sum.
        struct OverloadSkipRow
        {
        };
    }

    using Disjunctive2DProofMutation = std::variant<disjunctive_2d_proof_mutation::None, disjunctive_2d_proof_mutation::EmitNothing,
        disjunctive_2d_proof_mutation::SkipOneRefutation, disjunctive_2d_proof_mutation::SkipGuardWeakening,
        disjunctive_2d_proof_mutation::SkipEscapePins, disjunctive_2d_proof_mutation::OverloadSkipEnergy,
        disjunctive_2d_proof_mutation::OverloadSkipRow>;
}

#endif
