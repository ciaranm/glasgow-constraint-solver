#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REACHABLE_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REACHABLE_MUTATIONS_HH

#include <variant>

namespace gcs::innards::reachable
{
    /**
     * \brief Test-only corruptions of Reachable's proof steps, for the mutation
     * lanes registered against `run_test_and_expect_verify_failure.bash`.
     *
     * Every inference Reachable makes is a plain RUP whose whole content is its
     * reason, so the thing worth breaking is the reason. Each of these drops one
     * part of it and leaves the propagation alone: the solver behaves identically
     * and writes a proof veripb should refuse. A lane that verifies anyway is a
     * finding about the honest reason, not about the harness.
     *
     * \ingroup Innards
     */
    namespace reachable_proof_mutation
    {
        /// No corruption; the default.
        struct None
        {
        };

        /// Drop one of the literals that shut the border of the searched region,
        /// so the reason no longer says why the search stopped where it did.
        struct DropBorderLiteral
        {
        };

        /// Drop "this node is selected" from a root-filtering reason, leaving no
        /// reason why the candidate root had to reach anything.
        struct DropMandatoryNode
        {
        };

        /// Drop the root's remaining domain from an unreachable-node reason, so
        /// nothing says the root cannot be the node being ruled out.
        struct DropRootDomain
        {
        };
    }

    using ReachableProofMutation = std::variant<reachable_proof_mutation::None, reachable_proof_mutation::DropBorderLiteral,
        reachable_proof_mutation::DropMandatoryNode, reachable_proof_mutation::DropRootDomain>;
}

#endif
