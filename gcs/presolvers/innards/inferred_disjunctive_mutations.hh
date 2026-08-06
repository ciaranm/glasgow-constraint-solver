#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INNARDS_INFERRED_DISJUNCTIVE_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INNARDS_INFERRED_DISJUNCTIVE_MUTATIONS_HH

#include <variant>

/**
 * \file
 *
 * Deliberate corruptions of `InferredDisjunctive`'s proof steps, which exist so that a test can
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
     * \brief Deliberate corruptions of the assembled per-time certificate, for
     * testing only. VeriPB must reject each of them.
     *
     * The pieces this is built from each have their own mutations, and those
     * cover the pieces. What is left for these is the *assembly*: whether the
     * at-most-ones being merged really are about the tasks the clique claims,
     * whether the conclusion is the one the arithmetic supports, and whether a
     * pair that merely looks like a conflict can be smuggled in. Each of these
     * corrupts the conclusion rather than the route to it, since the route is
     * where a conflict-shaped derivation forgives everything.
     *
     * \ingroup Innards
     */
    namespace inferred_disjunctive_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Claim no member may run at all, rather than at most one.
        struct ClaimRhsZero
        {
        };

        /// Bridge one task's flags onto the *other* task's, so the at-most-one
        /// being merged is about a task the derivation never cornered.
        struct BridgeWrongTask
        {
        };

        /// Grow a clique with a task that does not conflict with its members ---
        /// the camouflage case, where a pair's demands sum to exactly the
        /// capacity and so are compatible by one unit. An off-by-one in the
        /// conflict test lands exactly here.
        struct IncludeNonConflicting
        {
        };

        /// Claim a makespan one larger than a posted clique's energy supports.
        /// The same discipline again, against the other thing a clique is used
        /// for: `L` is the number this whole exercise reports, so a derivation
        /// with slack in it would report it while proving something weaker.
        struct ClaimHigherMakespanBound
        {
        };
    }

    using InferredDisjunctiveMutation =
        std::variant<inferred_disjunctive_mutation::None, inferred_disjunctive_mutation::ClaimRhsZero, inferred_disjunctive_mutation::BridgeWrongTask,
            inferred_disjunctive_mutation::IncludeNonConflicting, inferred_disjunctive_mutation::ClaimHigherMakespanBound>;
}

#endif
