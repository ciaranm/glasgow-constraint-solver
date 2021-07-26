/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_HH 1

#include <gcs/constraint.hh>
#include <gcs/integer_variable.hh>

#include <vector>

namespace gcs
{
    class AllDifferent :
        public Constraint
    {
        private:
            const std::vector<IntegerVariableID> & _vars;

        public:
            explicit AllDifferent(const std::vector<IntegerVariableID> & vars);

            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void override;
    };
}

#endif