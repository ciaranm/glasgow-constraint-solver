/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HH 1

#include <gcs/constraint.hh>
#include <gcs/boolean_variable.hh>
#include <gcs/integer_variable.hh>

#include <variant>

namespace gcs
{
    class Equals :
        public Constraint
    {
        private:
            IntegerVariableID _v1, _v2;
            std::variant<bool, BooleanVariableID> _cond;

        public:
            explicit Equals(const IntegerVariableID v1, const IntegerVariableID v2, bool cond = true);
            explicit Equals(const IntegerVariableID v1, const IntegerVariableID v2, const BooleanVariableID reif_cond);

            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void override;
    };

    class NotEquals :
        public Equals
    {
        public:
            inline explicit NotEquals(const IntegerVariableID v1, const IntegerVariableID v2) :
                Equals(v1, v2, false)
            {
            };
    };
}

#endif
