#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_SUBCIRCUIT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_SUBCIRCUIT_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/circuit/subcircuit_base.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <variant>
#include <vector>

namespace gcs
{
    namespace subcircuit
    {
        /**
         * \brief Propagate SubCircuit by checking only: follow each chain of fixed
         * successors, and when one closes into a cycle, force every node outside that
         * cycle to be a self loop.
         *
         * This is Francis and Stuckey's `check`. It fires only on instantiation and does
         * no lookahead, so it is the cheapest option and the weakest.
         *
         * \ingroup Constraints
         */
        struct Check final
        {
        };

        /**
         * \brief Propagate SubCircuit by checking and preventing: as subcircuit::Check,
         * and additionally forbid a chain of fixed successors from closing into a cycle
         * whenever some node outside the chain is already known to be on the circuit.
         *
         * This is Francis and Stuckey's `check` plus `prevent`; `prevent` is not complete
         * on its own, so the two always go together. This is the default.
         *
         * The node outside the chain is their *evidence node*: unlike Circuit, where any
         * short cycle is a contradiction, a short cycle here is only wrong if some other
         * node cannot be a self loop, so nothing can be inferred until such a node exists.
         *
         * \ingroup Constraints
         */
        struct Prevent final
        {
        };

        /**
         * \brief Propagate SubCircuit by reachability as well: as subcircuit::Prevent, and
         * additionally require every node on the tour to lie in the same strongly connected
         * component as the node the caller named with with_required_node(), forcing anything
         * else to opt out.
         *
         * The tour is a cycle through the named node, so a node on it must both be reachable
         * from that node and reach it back; the two directions are checked by separate walks
         * and justified by separate arguments, and either can fire without the other.
         *
         * This is the connectivity part of Francis and Stuckey's `scc` algorithm -- their
         * rule for a strongly connected sub-component containing a required node, which is
         * the one component that always has one. Their four extra pruning rules -- prune
         * root, prune skip, fix required edges and prune within -- are not here yet; those
         * need the subtree structure of a depth-first traversal, where these two need only
         * the component.
         *
         * It needs with_required_node(), and does nothing without it: there is nothing to
         * be reachable *from* until some node is known to be on the tour, which is Francis
         * and Stuckey's own observation about applying this family to subcircuit at all.
         *
         * \ingroup Constraints
         */
        struct SCC final
        {
        };
    }

    /**
     * \brief The propagation algorithms supported by SubCircuit: subcircuit::Prevent (the
     * default), subcircuit::Check (cheaper and weaker) or subcircuit::SCC (stronger, and
     * only useful with with_required_node()). Requesting anything else is a compile-time
     * error, and the choice never changes the constraint's meaning or its proof encoding.
     *
     * \ingroup Constraints
     */
    using SubCircuitAlgorithm = std::variant<subcircuit::Check, subcircuit::Prevent, subcircuit::SCC>;

    /**
     * \brief SubCircuit constraint: requires the variables, representing graph nodes, to
     * take values such that each variable's value is the index of the next node on a
     * single tour, where a node not on the tour takes its own index as its value.
     *
     * This is MiniZinc's `subcircuit`, and the semantics have three corners worth stating
     * outright:
     *
     * - the **empty** subcircuit, every node pointing at itself, is a solution;
     * - the smallest non-empty one has **two** nodes, since a node pointing at itself is
     *   by definition off the tour, so there is no one-node cycle either to allow or to
     *   forbid;
     * - the successors are a permutation whether or not a node is on the tour, so
     *   all-different holds over the whole array. A node off the tour takes its own index,
     *   which is exactly what stops it being anyone else's successor.
     *
     * Circuit is the stricter constraint that additionally requires every node to be on
     * the tour; it is not a special case of this one, nor this one of it.
     *
     * The constructor takes only the successor array; configure propagation with the
     * fluent setters. Select the algorithm with with_algorithm() (subcircuit::Prevent by
     * default, or subcircuit::Check). Neither choice changes the constraint's meaning or
     * the OPB encoding written for proof logging.
     *
     * \ingroup Constraints
     */
    class SubCircuit : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _succ;
        SubCircuitAlgorithm _algorithm = subcircuit::Prevent{};
        bool _gac_all_different = false;
        std::optional<IntegerVariableID> _tour_size;
        std::optional<long> _required_node;
        bool _prune_root = false;

        // The node the position encoding is anchored on, settled by prepare(): what
        // with_required_node() named, or the lowest-numbered node whose declared domain
        // already says it is on the tour, or nothing when no node's does.
        std::optional<long> _anchor;

        // Backtrackable state allocated by prepare(), consumed by install_propagators().
        innards::subcircuit::SubCircuitStateHandles _state_handles;

        // The position-variable encoding, built by define_proof_model() and captured by
        // the algorithm's propagator. Empty when proof logging is off, which is what
        // both algorithms expect.
        innards::subcircuit::SubCircuitPosData _pos_data;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit SubCircuit(std::vector<IntegerVariableID> succ);

        /// Select the propagation algorithm: subcircuit::Prevent (the default) or
        /// subcircuit::Check. The choice selects propagation strength only and never
        /// changes the OPB encoding.
        auto with_algorithm(SubCircuitAlgorithm algorithm) -> SubCircuit &;

        /// Enforce all-different over the successors with a full generalised-arc-consistent
        /// propagator, in addition to the subcircuit propagation. Off by default (a cheaper
        /// value-consistent all-different is always applied regardless).
        auto with_gac_all_different(std::optional<bool> enable = true) -> SubCircuit &;

        /// Name a node that is already declared to be on the tour -- its own index must
        /// not be in its successor's domain, and this throws if it is. That is a
        /// precondition, not a strengthening: the constraint means exactly the same thing
        /// with and without it, so nothing about it is recorded in the `.scp`, in the same
        /// way the choice of algorithm is not.
        ///
        /// **Calling this is optional.** The constraint looks for such a node itself, and
        /// uses the lowest-numbered one it finds; naming one only overrides that choice,
        /// and turns "no node is declared on the tour" from something silently accepted
        /// into an error. Neither is a way to declare a node on the tour -- post a
        /// constraint for that, or give the variable a domain that says so.
        ///
        /// What an anchor buys is a cheaper proof. Without one, which edge of the tour
        /// wraps around is not known until the membership literals are, so every edge needs
        /// a row for each case and every certificate splits over the cycle's nodes. With
        /// one, only the edges into that node can wrap, which is exactly the shape Circuit
        /// gets for free by anchoring on node 0: half the rows, and one polish-notation step
        /// per certificate rather than one per node of the cycle.
        ///
        /// It also strengthens propagation, since a closed cycle that misses the anchor is
        /// a contradiction outright rather than something needing an evidence node, and it
        /// is what the SCC propagation needs, which cannot infer anything at all until some
        /// node is known to be on the tour.
        auto with_required_node(long node) -> SubCircuit &;

        /// Add Francis and Stuckey's *prune root* rule to subcircuit::SCC: try each value
        /// the anchor's successor could take, and remove any that would leave a node which
        /// must be on the tour unreachable from the anchor. Off by default, and ignored
        /// without subcircuit::SCC, which it strengthens rather than replaces.
        ///
        /// This is singleton arc consistency on the anchor's successor with respect to the
        /// reachability rule, which is at least what F&S's rule prunes: their condition ---
        /// that the edge leads to a subtree earlier than the last --- is a sufficient
        /// condition for the assumed edge stranding something, found cheaply from the
        /// depth-first traversal they already have, where this tries every value.
        ///
        /// **It is expensive, and deliberately so.** One reachability walk per candidate
        /// value, so `O(n^3)` work per propagator call against the plain rule's `O(n^2)`,
        /// and the certificate is a fresh `O(n^2)`-row induction per pruning. Measured on
        /// the MiniZinc Challenge `subcircuit` families the walk alone is already 87--98%
        /// of all propagation time and the node reduction it buys is 1.09--1.38x, so this
        /// is not switched on in the hope of going faster. It is here because the rule is
        /// certifiable and worth having implemented and checkable.
        auto with_prune_root(std::optional<bool> enable = true) -> SubCircuit &;

        /// Constrain how many nodes are on the tour: `size` is the number that do not
        /// point at themselves. This is XCSP3's `size` argument, for which MiniZinc's
        /// spelling has no equivalent.
        ///
        /// It is also how to ask for a *non-empty* tour, which XCSP3-core's `<circuit>`
        /// wants where MiniZinc's `subcircuit` does not: give `size` a lower bound of 2.
        /// There is no separate option for that, because this one already says it, and
        /// the count can never be 1 anyway -- a lone node has nowhere to point but itself,
        /// which is what taking its own index means.
        auto with_tour_size(IntegerVariableID size) -> SubCircuit &;

        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_SUBCIRCUIT_HH
