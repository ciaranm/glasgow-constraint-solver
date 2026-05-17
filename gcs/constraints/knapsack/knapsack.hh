#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief Knapsack constraint:
     * <code>sum(coefficients[x][i] * vars[i]) = totals[x]</code> for
     * each <code>x</code>. Coefficients and item domains must be
     * non-negative.
     *
     * Follows the same upfront-DAG pattern as BinPacking and MDD:
     * <code>prepare()</code> builds the statically-reduced layered DAG
     * once from the initial domains (forward reach from
     * <code>(0,...,0)</code> intersected with backward reach from
     * layer-n states whose every coordinate lies in
     * <code>initial dom(totals[x])</code>);
     * <code>install_initialiser</code> emits one-shot proof scaffolding
     * — per-coordinate <code>g_up</code> / <code>g_dn</code> reified
     * inequality flags and per-state conjunction flags — at
     * <code>ProofLevel::Top</code>; the per-call propagator does
     * forward+backward reachability against the current item and total
     * domains restricted to the static DAG and prunes items / total
     * bounds via <code>JustifyUsingRUP</code>. RUP closes through the
     * bridge reifications plus the natural per-equation OPB constraints.
     *
     * See <code>dev_docs/knapsack.md</code> for the staged design.
     *
     * For benchmarking against the original (per-call DP) implementation,
     * see KnapsackLegacy.
     *
     * \ingroup Constraints
     */
    class Knapsack : public Constraint
    {
    private:
        struct DagBridge;

        std::vector<std::vector<Integer>> _coeffs;
        std::vector<IntegerVariableID> _vars;
        std::vector<IntegerVariableID> _totals;
        std::shared_ptr<DagBridge> _bridge;
        std::optional<innards::ConstraintStateHandle> _dead_cache_handle;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Knapsack(std::vector<Integer> weights, std::vector<Integer> profits, std::vector<IntegerVariableID> vars, IntegerVariableID weight,
            IntegerVariableID profit);

        explicit Knapsack(std::vector<std::vector<Integer>> coefficients, std::vector<IntegerVariableID> vars, std::vector<IntegerVariableID> totals);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
