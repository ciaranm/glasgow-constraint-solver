#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REACHABLE_REACHABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REACHABLE_REACHABLE_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/reachable/mutations.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <memory>
#include <utility>
#include <vector>

namespace gcs
{
    namespace innards::reachable
    {
        /**
         * \brief The shared implementation of Reachable and DReachable, which differ
         * only in whether an edge may be followed in both directions.
         *
         * \ingroup Innards
         */
        class ReachableBase : public Constraint
        {
        protected:
            std::vector<std::pair<std::size_t, std::size_t>> _edges;
            IntegerVariableID _root;
            std::vector<IntegerVariableID> _ns;
            std::vector<IntegerVariableID> _es;
            bool _directed;
            ReachableProofMutation _proof_mutation = reachable_proof_mutation::None{};

            explicit ReachableBase(std::vector<std::pair<std::size_t, std::size_t>> edges, IntegerVariableID root, std::vector<IntegerVariableID> ns,
                std::vector<IntegerVariableID> es, bool directed);

            virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
            virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
            virtual auto install_propagators(innards::Propagators &) -> void override;

            /// The `.scp` term shared by both spellings: the two endpoint arrays, the
            /// root, then the node and edge arrays.
            [[nodiscard]] auto base_s_expr(const innards::ProofModel * const) const -> innards::SExpr;

        public:
            /// Testing only: corrupt one part of every reason this constraint gives,
            /// so a mutation lane can check that veripb refuses the result. See
            /// ReachableProofMutation. Never use this outside a test.
            auto with_proof_mutation(ReachableProofMutation mutation) -> ReachableBase &;
        };
    }

    /**
     * \brief Constrain the subgraph given by `ns` and `es` of an undirected graph to
     * be reachable from `root`, matching MiniZinc's `reachable`.
     *
     * Nodes are numbered from zero and `edges[e]` gives edge `e`'s two endpoints;
     * `ns[i]` and `es[e]` are 0/1 variables saying whether node `i` and edge `e` are
     * in the subgraph, and `root` takes a node number. Every selected edge must have
     * both its endpoints selected (MiniZinc's `subgraph`), the root must be selected,
     * and every selected node must be reachable from the root along selected edges,
     * following each in either direction.
     *
     * The root being selected means the subgraph is never empty, which is what
     * MiniZinc's `fzn_dreachable` says.
     *
     * Propagation is generalised-arc-consistent on what it removes --- a 1 leaves an
     * `ns` or `es` domain, and a value leaves the root's domain, exactly when it has
     * no support --- and does not force nodes or edges *in* beyond what `subgraph`
     * and the root require. That gap is precisely the cut vertices and bridges of
     * the residual graph, which for the undirected spelling is precisely the rest of
     * GAC, and which certifies in a single RUP wherever the root is fixed; see
     * dev_docs/connectivity-proofs.md.
     *
     * Passing the same variable for two nodes (or two edges) is handled rather
     * than rejected: it simply means those nodes are selected together, and both
     * the propagator and the OPB read it that way. As elsewhere, consistency is
     * not claimed under aliasing.
     *
     * `connected` is this with the root existentially quantified, which is what
     * MiniZinc's `fzn_connected` spells as `let { var index_set(ns): r } in
     * reachable(...)`: create a root variable over `0 .. ns.size() - 1` on the
     * Problem and post Reachable against it. The root has to be a Problem variable
     * rather than one this constraint allocates for itself, because search only
     * branches on Problem variables and nothing determines the root by propagation.
     *
     * \ingroup Constraints
     */
    class Reachable : public innards::reachable::ReachableBase
    {
    public:
        explicit Reachable(std::vector<std::pair<std::size_t, std::size_t>> edges, IntegerVariableID root, std::vector<IntegerVariableID> ns,
            std::vector<IntegerVariableID> es);

        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief As Reachable, but each edge may only be followed from `edges[e].first`
     * to `edges[e].second`. Matches MiniZinc's `dreachable`.
     *
     * `dconnected` is this with the root existentially quantified; see Reachable.
     *
     * \ingroup Constraints
     */
    class DReachable : public innards::reachable::ReachableBase
    {
    public:
        explicit DReachable(std::vector<std::pair<std::size_t, std::size_t>> edges, IntegerVariableID root, std::vector<IntegerVariableID> ns,
            std::vector<IntegerVariableID> es);

        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REACHABLE_REACHABLE_HH
