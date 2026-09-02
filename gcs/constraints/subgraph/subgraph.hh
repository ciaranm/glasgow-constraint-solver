#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SUBGRAPH_SUBGRAPH_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SUBGRAPH_SUBGRAPH_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <memory>
#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief Every selected edge has both its endpoints selected, matching
     * MiniZinc's `subgraph`.
     *
     * Nodes are numbered from zero and `edges[e]` gives edge `e`'s two endpoints;
     * `ns[i]` and `es[e]` are 0/1 variables saying whether node `i` and edge `e`
     * are in the selected subgraph. Nothing requires a node to be in an edge, so
     * an all-zero assignment is a solution, as it is in MiniZinc.
     *
     * This is two implications per edge, and unit propagation over them is all
     * there is to it, so the constraint exists for the sake of the C++ and `.scp`
     * interfaces rather than because it infers anything a decomposition would not.
     * Propagation is generalised-arc-consistent, which the tests check.
     *
     * Reachable and DReachable enforce this themselves, and so do Tree, DTree,
     * Path and DPath through the reachability child they install, so posting it
     * alongside one of those is redundant rather than wrong.
     *
     * \ingroup Constraints
     */
    class Subgraph : public Constraint
    {
    private:
        std::vector<std::pair<std::size_t, std::size_t>> _edges;
        std::vector<IntegerVariableID> _ns, _es;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Subgraph(
            std::vector<std::pair<std::size_t, std::size_t>> edges, std::vector<IntegerVariableID> ns, std::vector<IntegerVariableID> es);

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SUBGRAPH_SUBGRAPH_HH
