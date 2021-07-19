/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_REIF_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_REIF_HH 1

#include <gcs/constraint.hh>
#include <gcs/boolean_variable.hh>
#include <gcs/integer_variable.hh>

namespace gcs
{
    class EqualsReif :
        public Constraint
    {
        private:
            IntegerVariableID _v1, _v2;
            BooleanVariableID _cond;

        public:
            explicit EqualsReif(const IntegerVariableID v1, const IntegerVariableID v2, const BooleanVariableID cond);

            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void override;
    };
}

#endif
