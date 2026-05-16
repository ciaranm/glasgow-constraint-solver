#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/variable_id.hh>

#include <memory>
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
     * This is the new (upfront-DAG) implementation following the same
     * pattern as BinPacking and MDD: <code>prepare()</code> builds
     * static structures from initial domains, <code>install_initialiser</code>
     * emits one-shot proof scaffolding at <code>ProofLevel::Top</code>,
     * and the per-call propagator reads both via a shared
     * <code>shared_ptr</code> bridge.
     *
     * \note Stage 1: only the all-fixed checker is implemented. When
     * every item variable is single-valued, each <code>totals[x]</code>
     * is fixed to the computed sum (RUP from the natural OPB equation
     * plus the assigned-item literals). No mid-search pruning yet;
     * Stage 2 will add the static DAG and per-call GAC.
     *
     * For benchmarking against the previous implementation, see
     * KnapsackLegacy.
     *
     * \ingroup Constraints
     */
    class Knapsack : public Constraint
    {
    private:
        std::vector<std::vector<Integer>> _coeffs;
        std::vector<IntegerVariableID> _vars;
        std::vector<IntegerVariableID> _totals;

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
