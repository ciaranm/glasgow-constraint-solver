#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TREE_TREE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TREE_TREE_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/graph_rules.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <memory>
#include <utility>
#include <vector>

namespace gcs
{
    namespace innards::tree
    {
        /**
         * \brief The shared implementation of Tree and DTree, which differ in
         * whether an edge may be followed in both directions and in whether the
         * degree rules below are needed at all.
         *
         * \ingroup Innards
         */
        class TreeBase : public Constraint
        {
        protected:
            std::vector<std::pair<std::size_t, std::size_t>> _edges;
            IntegerVariableID _root;
            std::vector<IntegerVariableID> _ns, _es;
            bool _directed;
            std::vector<innards::graph_rules::Rule> _rules;

            explicit TreeBase(std::vector<std::pair<std::size_t, std::size_t>> edges, IntegerVariableID root, std::vector<IntegerVariableID> ns,
                std::vector<IntegerVariableID> es, bool directed);

            virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
            virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
            virtual auto install_propagators(innards::Propagators &) -> void override;

            /// The `.scp` term shared by both spellings, matching Reachable's.
            [[nodiscard]] auto base_s_expr(const innards::ProofModel * const) const -> innards::SExpr;
        };
    }

    /**
     * \brief Constrain the subgraph given by `ns` and `es` of an undirected graph
     * to be a tree rooted at `root`, matching MiniZinc's `tree`.
     *
     * Arguments are Reachable's: nodes numbered from zero, `edges[e]` giving edge
     * `e`'s two endpoints, and 0/1 variables per node and per edge.
     *
     * This is exactly `Reachable` plus `sum(es) = sum(ns) - 1`, and it is posted
     * as those two constraints rather than propagated as one: a connected
     * subgraph with one fewer edge than nodes is a tree, and a tree is connected
     * with one fewer edge than nodes. The stdlib's `fzn_tree` instead doubles
     * every edge and adds a parent-and-distance labelling, which is what makes
     * `tree` expensive to propagate and far more expensive to prove; see
     * dev_docs/connectivity-proofs.md.
     *
     * Propagation is **not** generalised-arc-consistent, and the tests say so:
     * `Reachable` is GAC and the cardinality equality is GAC, but their
     * conjunction is not. In particular nothing here notices that a selected edge
     * would close a cycle until the count runs out. A union-find cycle check
     * would close that gap and is the obvious later strengthening.
     *
     * \ingroup Constraints
     */
    class Tree : public innards::tree::TreeBase
    {
    public:
        explicit Tree(std::vector<std::pair<std::size_t, std::size_t>> edges, IntegerVariableID root, std::vector<IntegerVariableID> ns,
            std::vector<IntegerVariableID> es);

        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief As Tree, but each edge may only be followed from `edges[e].first` to
     * `edges[e].second`, so the subgraph is an arborescence. Matches MiniZinc's
     * `dtree`.
     *
     * `DReachable` plus `sum(es) = sum(ns) - 1` plus at most one selected edge
     * entering each node. Those three say arborescence between them: every
     * selected node is reached from the root, so each non-root one has an edge
     * coming in, and at most one does; the count then leaves the root with none.
     * The stdlib's `fzn_dtree` says the same thing with a parent function, which
     * is where its distance labelling comes from.
     *
     * Not generalised-arc-consistent, for the reason given on Tree.
     *
     * \ingroup Constraints
     */
    class DTree : public innards::tree::TreeBase
    {
    public:
        explicit DTree(std::vector<std::pair<std::size_t, std::size_t>> edges, IntegerVariableID root, std::vector<IntegerVariableID> ns,
            std::vector<IntegerVariableID> es);

        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TREE_TREE_HH
