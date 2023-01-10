/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_N_VALUE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_N_VALUE_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that a variable is equal to the number of distinct
     * values among the array of variables.
     *
     * \ingroup Constraints
     * \sa AllDifferent
     */
    class NValue : public Constraint
    {
    private:
        IntegerVariableID _n_values;
        const std::vector<IntegerVariableID> _vars;

    public:
        explicit NValue(const IntegerVariableID &, std::vector<IntegerVariableID>);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
