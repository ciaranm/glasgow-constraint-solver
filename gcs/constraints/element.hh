/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ELEMENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ELEMENT_HH 1

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    class Element :
        public Constraint
    {
        private:
            IntegerVariableID _var, _idx_var;
            const std::vector<IntegerVariableID> & _vars;

        public:
            explicit Element(IntegerVariableID var, IntegerVariableID idx_var, const std::vector<IntegerVariableID> & vars);

            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void override;
    };
}

#endif
