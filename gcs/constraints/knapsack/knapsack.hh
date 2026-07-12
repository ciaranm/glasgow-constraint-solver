#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/variable_id.hh>

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
     * This is the default implementation: it builds its DP table and
     * proof scaffolding from scratch on every propagation call, at
     * <code>ProofLevel::Temporary</code>. It is chosen as the default
     * because its proofs verify substantially faster (3.6–18×) than the
     * upfront-DAG alternative.
     *
     * For an opt-in variant that emits upfront paper-style proof
     * scaffolding once at the search root — producing 3–6× smaller proofs
     * at the cost of slower verification — see KnapsackUpfront. Prefer it
     * only when proof size or distribution matters. See
     * <code>dev_docs/knapsack.md</code> for the measured rationale.
     *
     * \ingroup Constraints
     */
    class Knapsack : public Constraint
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
