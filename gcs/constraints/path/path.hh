#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PATH_PATH_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PATH_PATH_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/graph_rules.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <memory>
#include <utility>
#include <vector>

namespace gcs
{
    namespace innards::path
    {
        /**
         * \brief The shared implementation of Path and DPath, which differ in
         * whether an edge may be followed in both directions and so in which
         * degree rules pin the two ends down.
         *
         * \ingroup Innards
         */
        class PathBase : public Constraint
        {
        protected:
            std::vector<std::pair<std::size_t, std::size_t>> _edges;
            IntegerVariableID _start, _end;
            std::vector<IntegerVariableID> _ns, _es;
            bool _directed;
            std::vector<innards::graph_rules::Rule> _rules;

            explicit PathBase(std::vector<std::pair<std::size_t, std::size_t>> edges, IntegerVariableID start, IntegerVariableID end,
                std::vector<IntegerVariableID> ns, std::vector<IntegerVariableID> es, bool directed);

            virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
            virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
            virtual auto install_propagators(innards::Propagators &) -> void override;

            /// The `.scp` term shared by both spellings.
            [[nodiscard]] auto base_s_expr(const innards::ProofModel * const) const -> innards::SExpr;
        };
    }

    /**
     * \brief Constrain the subgraph given by `ns` and `es` of an undirected graph
     * to be a path from `start` to `end`, matching MiniZinc's `path`.
     *
     * Arguments are Reachable's, plus the two endpoints, which may be variables.
     * `start` and `end` may be the same, in which case the only solution selects
     * that node and no edges.
     *
     * Posted as `Reachable` from `start`, plus `sum(es) = sum(ns) - 1`, plus a
     * handful of degree rules: no selected node has more than two selected edges,
     * and the two endpoints have at most one each. That is enough --- a connected
     * subgraph with one fewer edge than nodes is a tree, and a tree whose degrees
     * are all at most two is a path, whose ends are then exactly the nodes of
     * degree one. One reachability encoding does it, where the stdlib's `fzn_path`
     * doubles every edge and then asks for two spanning trees.
     *
     * Note that `start` needing at most one incident edge is what makes the
     * `start = end` case come out right, together with reachability: with no edge
     * leaving it, nothing else is reachable, so the subgraph is that node alone.
     *
     * Propagation is **not** generalised-arc-consistent; see Tree.
     *
     * \ingroup Constraints
     */
    class Path : public innards::path::PathBase
    {
    public:
        explicit Path(std::vector<std::pair<std::size_t, std::size_t>> edges, IntegerVariableID start, IntegerVariableID end,
            std::vector<IntegerVariableID> ns, std::vector<IntegerVariableID> es);

        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief As Path, but each edge may only be followed from `edges[e].first` to
     * `edges[e].second`. Matches MiniZinc's `dpath`.
     *
     * `DReachable` from `start`, plus `sum(es) = sum(ns) - 1`, plus at most one
     * selected edge into and out of each node, nothing into `start`, and nothing
     * out of `end`, which also has to be selected. The stdlib's `fzn_dpath` says
     * this as two `dtree`s, one on the graph and one on its reverse; one
     * reachability encoding is enough, because out-degree at most one already
     * stops the walk from `start` branching.
     *
     * Propagation is **not** generalised-arc-consistent; see Tree.
     *
     * \ingroup Constraints
     */
    class DPath : public innards::path::PathBase
    {
    public:
        explicit DPath(std::vector<std::pair<std::size_t, std::size_t>> edges, IntegerVariableID start, IntegerVariableID end,
            std::vector<IntegerVariableID> ns, std::vector<IntegerVariableID> es);

        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PATH_PATH_HH
