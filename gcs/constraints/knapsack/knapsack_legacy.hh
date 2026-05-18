#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_LEGACY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_LEGACY_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/variable_id.hh>

#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief Legacy Knapsack propagator: builds its DP table and proof
     * scaffolding from scratch on every propagation call, at
     * <code>ProofLevel::Temporary</code>.
     *
     * This is the original implementation, retained for benchmarking
     * against the new (upfront-DAG) Knapsack. New code should post
     * Knapsack instead.
     *
     * Constraint: <code>sum(coefficients[x][i] * vars[i]) = totals[x]</code>
     * for each <code>x</code>. Coefficients and item domains must be
     * non-negative.
     *
     * \ingroup Constraints
     */
    class KnapsackLegacy : public Constraint
    {
    private:
        const std::vector<std::vector<Integer>> _coeffs;
        const std::vector<IntegerVariableID> _vars;
        const std::vector<IntegerVariableID> _totals;
        std::vector<std::pair<innards::ProofLine, innards::ProofLine>> _eqns_lines;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit KnapsackLegacy(std::vector<Integer> weights, std::vector<Integer> profits,
            std::vector<IntegerVariableID> vars, IntegerVariableID weight, IntegerVariableID profit);

        explicit KnapsackLegacy(std::vector<std::vector<Integer>> coefficients,
            std::vector<IntegerVariableID> vars,
            std::vector<IntegerVariableID> totals);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
