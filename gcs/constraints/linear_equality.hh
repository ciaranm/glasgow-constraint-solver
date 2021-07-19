/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_EQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_EQUALITY_HH 1

#include <gcs/constraint.hh>
#include <gcs/integer.hh>
#include <gcs/linear.hh>

#include <vector>

namespace gcs
{
    class LinearEquality :
        public Constraint
    {
        private:
            Linear _coeff_vars;
            Integer _value;

        public:
            explicit LinearEquality(Linear && coeff_vars, Integer value);

            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void override;
    };
}

#endif
