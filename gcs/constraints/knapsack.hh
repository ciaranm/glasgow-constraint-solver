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
        const std::vector<Integer> _weights, _profits;
        const std::vector<IntegerVariableID> _vars;
        const IntegerVariableID _weight;
        const IntegerVariableID _profit;

    public:
        explicit Knapsack(std::vector<Integer> weights, std::vector<Integer> profits,
            std::vector<IntegerVariableID> vars, IntegerVariableID weight, IntegerVariableID profit);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
