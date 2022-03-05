/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COUNT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COUNT_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    class Count : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> & _vars;
        IntegerVariableID _value_of_interest, _how_many;

    public:
        explicit Count(const std::vector<IntegerVariableID> &, const IntegerVariableID & value_of_interest, const IntegerVariableID & how_many);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };
}

#endif
