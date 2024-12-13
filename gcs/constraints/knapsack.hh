#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Knapsack constraint, <code>sum(weights[i]*vars[i]) = weight</code> and
     * <code>sum(profits[i]*vars[i]) = profit</code>.
     *
     * \ingroup Constraints
     */
    class Knapsack : public Constraint
    {
    private:
        const std::vector<std::vector<Integer>> _coeffs;
        const std::vector<IntegerVariableID> _vars;
        const std::vector<IntegerVariableID> _totals;

    public:
        explicit Knapsack(std::vector<Integer> weights, std::vector<Integer> profits,
            std::vector<IntegerVariableID> vars, IntegerVariableID weight, IntegerVariableID profit);

        explicit Knapsack(std::vector<std::vector<Integer>> coefficients,
            std::vector<IntegerVariableID> vars,
            std::vector<IntegerVariableID> totals);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
