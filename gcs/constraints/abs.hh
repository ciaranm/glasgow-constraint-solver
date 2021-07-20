/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HH 1

#include <gcs/constraint.hh>
#include <gcs/integer_variable.hh>

namespace gcs
{
    class Abs :
        public Constraint
    {
        private:
            IntegerVariableID _v1, _v2;

        public:
            explicit Abs(const IntegerVariableID v1, const IntegerVariableID v2);

            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void override;
    };
}

#endif
