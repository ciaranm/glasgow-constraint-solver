#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DAG_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DAG_MUTATIONS_HH

#include <variant>

namespace gcs::innards::dag
{
    /**
     * \brief Test-only corruptions of Dag's proof steps, for the mutation lanes
     * registered against `run_test_and_expect_verify_failure.bash`.
     *
     * Every inference Dag makes is a plain RUP whose whole content is its reason,
     * and there are only two shapes of reason to break: the selected edges of the
     * path that closes a cycle, and the one endpoint literal behind a subgraph
     * inference. Each mutation drops one part and leaves the propagation alone,
     * so the solver behaves identically and writes a proof veripb should refuse.
     * A lane that verifies anyway is a finding about the honest reason, not about
     * the harness.
     *
     * \ingroup Innards
     */
    namespace dag_proof_mutation
    {
        /// No corruption; the default.
        struct None
        {
        };

        /// Drop one of the selected edges of the path that would close the cycle,
        /// so the reason no longer traces a cycle at all.
        struct DropPathEdge
        {
        };

        /// Drop the single endpoint literal behind a subgraph inference, leaving
        /// nothing that says why the edge had to go.
        struct DropEndpointLiteral
        {
        };
    }

    using DagProofMutation = std::variant<dag_proof_mutation::None, dag_proof_mutation::DropPathEdge, dag_proof_mutation::DropEndpointLiteral>;
}

#endif
