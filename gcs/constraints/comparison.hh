/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH 1

#include <gcs/constraint.hh>
#include <gcs/boolean_variable.hh>
#include <gcs/integer_variable.hh>

#include <variant>

namespace gcs
{
    enum class ComparisonOperator
    {
        Equals,
        LessThan
    };

    class ComparisonReif :
        public Constraint
    {
        private:
            IntegerVariableID _v1, _v2;
            std::variant<bool, BooleanVariableID> _cond;
            ComparisonOperator _op;

            auto _convert_to_low_level_equals(LowLevelConstraintStore &, const State &) && -> void;
            auto _convert_to_low_level_less_than(LowLevelConstraintStore &, const State &) && -> void;

        public:
            explicit ComparisonReif(const IntegerVariableID v1, const IntegerVariableID v2, bool cond, ComparisonOperator op);
            explicit ComparisonReif(const IntegerVariableID v1, const IntegerVariableID v2, const BooleanVariableID reif_cond, ComparisonOperator op);

            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void override;
    };

    class Equals :
        public ComparisonReif
    {
        public:
            inline explicit Equals(const IntegerVariableID v1, const IntegerVariableID v2) :
                ComparisonReif(v1, v2, true, ComparisonOperator::Equals)
            {
            };
    };

    class NotEquals :
        public ComparisonReif
    {
        public:
            inline explicit NotEquals(const IntegerVariableID v1, const IntegerVariableID v2) :
                ComparisonReif(v1, v2, false, ComparisonOperator::Equals)
            {
            };
    };

    class LessThan :
        public ComparisonReif
    {
        public:
            inline explicit LessThan(const IntegerVariableID v1, const IntegerVariableID v2) :
                ComparisonReif(v1, v2, true, ComparisonOperator::LessThan)
            {
            };
    };
}

#endif
