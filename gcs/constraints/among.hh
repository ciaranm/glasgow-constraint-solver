#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_AMONG_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_AMONG_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain the number of times that a set of constant values appear
     * in an array of variables.
     *
     * \ingroup Constraints
     */
    class Among : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        const std::vector<Integer> _values_of_interest;
        IntegerVariableID _how_many;

    public:
        explicit Among(std::vector<IntegerVariableID>, const std::vector<Integer> & values_of_interest, const IntegerVariableID & how_many);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
