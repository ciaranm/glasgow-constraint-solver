#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INNARDS_INFERRED_CUMULATIVE_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INNARDS_INFERRED_CUMULATIVE_MUTATIONS_HH

#include <variant>

/**
 * \file
 *
 * Deliberate corruptions of `InferredCumulative`'s proof steps, which exist so that a test can
 * show the honest derivation is tight to what it claims. They live here, in the
 * innards, rather than beside the presolver they corrupt: the header a user
 * includes to run it should not also advertise a way to make the solver emit
 * deliberately wrong proofs. Issue #669; see
 * gcs/constraints/innards/cumulative_mutations.hh for why compiling them out of
 * release builds was rejected.
 */

namespace gcs::innards
{
    /**
     * \brief Deliberate corruptions of a lifted cut's certificate, for testing
     * only. VeriPB must reject each of them.
     *
     * The first two are the signature test of a lifted constraint: claim one
     * better than was derived and require a rejection. With small,
     * close-together integers a slack derivation can verify by coincidence ---
     * a `pol` that lands somewhere weaker than intended still lands somewhere
     * true --- and only a `+1` that is *refused* says the honest line is tight
     * to what the constraint goes on to assume of it.
     *
     * \ingroup Innards
     */
    namespace inferred_cumulative_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Pin one less capacity than the derivation supports.
        struct ClaimTighterCapacity
        {
        };

        /// Pin one more height for the first member than the derivation
        /// supports.
        struct ClaimTallerTask
        {
        };

        /// Build the dynamic programme against a capacity one smaller than the
        /// donor's row, so that its states claim the row rules out a member it
        /// does not. Unlike the two above, this corrupts the *derivation* rather
        /// than what is claimed of it, and is caught inside the replay rather
        /// than at the pin.
        struct ClaimTighterRow
        {
        };

        /// Claim a makespan one larger than a posted cut's energy supports.
        /// The same discipline again, against the other thing a cut is used
        /// for: `L` is the number this whole exercise reports, so a derivation
        /// with slack in it would report it while proving something weaker.
        struct ClaimHigherMakespanBound
        {
        };

        /// Carry a resource's row onto the *wrong* member's flags when a cut
        /// spans more than one of them, so that the row a state is ruled out by
        /// is about a task other than the one it names.
        ///
        /// The corruption a cut over several resources adds over one over a
        /// single resource: nothing else in this list touches the crossing, and
        /// with one donor there is no crossing to touch --- so a fixture for
        /// this has to be genuinely multi-resource, which is the point of
        /// having it.
        struct BridgeWrongTask
        {
        };
    }

    using InferredCumulativeMutation = std::variant<inferred_cumulative_mutation::None, inferred_cumulative_mutation::ClaimTighterCapacity,
        inferred_cumulative_mutation::ClaimTallerTask, inferred_cumulative_mutation::ClaimTighterRow,
        inferred_cumulative_mutation::ClaimHigherMakespanBound, inferred_cumulative_mutation::BridgeWrongTask>;
}

#endif
