#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DAG_DAG_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DAG_DAG_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/dag/mutations.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <memory>
#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain the subgraph given by `ns` and `es` of a fixed directed
     * graph to be acyclic, matching MiniZinc's `dag`.
     *
     * Nodes are numbered from zero and `edges[e]` gives edge `e`'s tail and head;
     * `ns[i]` and `es[e]` are 0/1 variables saying whether node `i` and edge `e`
     * are in the selected subgraph. Every selected edge must have both its
     * endpoints selected (MiniZinc's `subgraph`), and the selected edges must
     * contain no directed cycle. An all-zero assignment is a solution.
     *
     * **This is stricter than MiniZinc's own decomposition, deliberately.**
     * `fzn_dreachable` calls `subgraph` explicitly; `fzn_dag` does not, and its
     * distance labelling only forces an edge's *head* to be selected. So the
     * stdlib admits a selected edge leaving an unselected node, and this does
     * not: on a two node graph with the one edge 0 to 1, the decomposition has
     * six solutions and this has five. Chuffed's native `dag` disagrees with both
     * and has four, requiring weak connectivity as well. The documented meaning is
     * "the subgraph `ns` and `es` ... is a DAG", so this follows the documentation
     * and Reachable rather than the decomposition; a decomposition-against-
     * propagator comparison will not agree on solution counts, and that is the
     * reason, not a bug. See dev_docs/connectivity-proofs.md.
     *
     * Propagation is generalised-arc-consistent, which the constraint's own tests
     * check with solve_for_tests_checking_gac. Acyclicity is downward closed --- a
     * subset of an acyclic selection is acyclic --- so nothing is ever forced *in*
     * except through the subgraph rows, and an edge may stay out exactly when
     * adding it to the already selected edges would close a cycle. That is the
     * whole of consistency here, so unlike Reachable there are no cut vertices,
     * no dominators and no case split over an existentially quantified root.
     *
     * Passing the same variable for two nodes (or two edges) is handled rather
     * than rejected: it simply means those nodes are selected together, and both
     * the propagator and the OPB read it that way. As elsewhere, consistency is
     * not claimed under aliasing.
     *
     * \ingroup Constraints
     */
    class Dag : public Constraint
    {
    private:
        std::vector<std::pair<std::size_t, std::size_t>> _edges;
        std::vector<IntegerVariableID> _ns, _es;
        innards::dag::DagProofMutation _proof_mutation = innards::dag::dag_proof_mutation::None{};

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Dag(std::vector<std::pair<std::size_t, std::size_t>> edges, std::vector<IntegerVariableID> ns, std::vector<IntegerVariableID> es);

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;

        /// Testing only: corrupt one part of every reason this constraint gives,
        /// so a mutation lane can check that veripb refuses the result. See
        /// DagProofMutation. Never use this outside a test.
        auto with_proof_mutation(innards::dag::DagProofMutation mutation) -> Dag &;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DAG_DAG_HH
