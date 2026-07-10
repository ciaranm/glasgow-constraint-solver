#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_CIRCUIT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_CIRCUIT_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/constraints/circuit/circuit_prevent.hh>
#include <gcs/constraints/circuit/circuit_scc.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <variant>
#include <vector>

namespace gcs
{
    namespace circuit
    {
        /**
         * \brief Propagate Circuit by finding strongly connected components: prune edges that
         * cannot lie on any Hamiltonian cycle, force required edges, and prevent small cycles.
         *
         * This is the default. It propagates more strongly than circuit::Prevent, at a higher
         * cost per search node.
         *
         * \ingroup Constraints
         */
        struct SCC final
        {
        };

        /**
         * \brief Propagate Circuit by the cheaper "prevent" method: track the chains formed by
         * fixed successor edges and forbid (or force) each chain from closing into a short cycle.
         *
         * \ingroup Constraints
         */
        struct Prevent final
        {
        };
    }

    /**
     * \brief The propagation algorithms supported by Circuit: circuit::SCC (the stronger default)
     * or circuit::Prevent (cheaper). Requesting anything else is a compile-time error, and the
     * choice never changes the constraint's meaning or its proof encoding.
     *
     * \ingroup Constraints
     */
    using CircuitAlgorithm = std::variant<circuit::SCC, circuit::Prevent>;

    /**
     * \brief Circuit constraint: requires the variables, representing graph nodes, take values
     * such that each variable's value is the index of the next node in a single tour visiting
     * every variable.
     *
     * The constructor takes only the successor array; configure propagation with the fluent
     * setters. Select the algorithm with with_algorithm() (circuit::SCC by default, or
     * circuit::Prevent). The SCC-only tuning knobs (with_prune_root(), with_prune_skip(), ...)
     * are no-ops under circuit::Prevent. None of these choices change the constraint's meaning
     * or the OPB encoding written for proof logging.
     *
     * \ingroup Constraints
     */
    class Circuit : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _succ;
        CircuitAlgorithm _algorithm = circuit::SCC{};
        bool _gac_all_different = false;
        SCCOptions _scc_options{};

        auto set_up(innards::Propagators &, innards::State &, innards::ProofModel * const) -> innards::circuit::PosVarDataMap;

    public:
        explicit Circuit(std::vector<IntegerVariableID> succ);

        /// Select the propagation algorithm: circuit::SCC (the default) or circuit::Prevent.
        /// The choice selects propagation strength only and never changes the OPB encoding.
        auto with_algorithm(CircuitAlgorithm algorithm) -> Circuit &;

        /// Enforce all-different over the successors with a full generalised-arc-consistent
        /// propagator, in addition to the circuit propagation. Off by default (a cheaper
        /// value-consistent all-different is always applied regardless).
        auto with_gac_all_different(std::optional<bool> enable = true) -> Circuit &;

        /// SCC-only: prune impossible edges out of the root node. No-op under circuit::Prevent.
        auto with_prune_root(std::optional<bool> enable = true) -> Circuit &;
        /// SCC-only: prune edges that would skip over a mandatory subtree. No-op under circuit::Prevent.
        auto with_prune_skip(std::optional<bool> enable = true) -> Circuit &;
        /// SCC-only: fix required (back-)edges. No-op under circuit::Prevent.
        auto with_fix_req(std::optional<bool> enable = true) -> Circuit &;
        /// SCC-only: prune impossible edges within a subtree. No-op under circuit::Prevent.
        auto with_prune_within(std::optional<bool> enable = true) -> Circuit &;
        /// SCC-only: prove pruning by a dominance argument rather than reachability. No-op under circuit::Prevent.
        auto with_prove_using_dominance(std::optional<bool> enable = true) -> Circuit &;
        /// SCC-only: emit explanatory proof comments. No-op under circuit::Prevent.
        auto with_enable_comments(std::optional<bool> enable = true) -> Circuit &;
        /// SCC-only: prove at-most-one position facts by contradiction. No-op under circuit::Prevent.
        auto with_prove_am1_by_contradiction(std::optional<bool> enable = true) -> Circuit &;
        /// SCC-only: reify a short "reason" flag rather than citing the full reason each time. No-op under circuit::Prevent.
        auto with_short_reasons(std::optional<bool> enable = true) -> Circuit &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_CIRCUIT_HH
