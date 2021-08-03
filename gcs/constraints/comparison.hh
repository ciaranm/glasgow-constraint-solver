/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH 1

#include <gcs/constraint.hh>
#include <gcs/literal.hh>
#include <gcs/integer_variable.hh>
#include <gcs/boolean_variable.hh>

namespace gcs
{
    enum class ComparisonOperator
    {
        Equals,
        LessThan,
        LessThanEqual
    };

    class ComparisonReif :
        public Constraint
    {
        private:
            IntegerVariableID _v1, _v2;
            Literal _cond;
            bool _full_reif;
            ComparisonOperator _op;

            auto _convert_to_low_level_equals(LowLevelConstraintStore &, const State &) && -> void;
            auto _convert_to_low_level_less_than(LowLevelConstraintStore &, const State &, bool equal) && -> void;

        public:
            explicit ComparisonReif(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond, bool full_reif, ComparisonOperator op);

            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void override;
    };

    class Equals :
        public ComparisonReif
    {
        public:
            inline explicit Equals(const IntegerVariableID v1, const IntegerVariableID v2) :
                ComparisonReif(v1, v2, +constant_variable(true), true, ComparisonOperator::Equals)
            {
            };
    };

    class NotEquals :
        public ComparisonReif
    {
        public:
            inline explicit NotEquals(const IntegerVariableID v1, const IntegerVariableID v2) :
                ComparisonReif(v1, v2, +constant_variable(false), true, ComparisonOperator::Equals)
            {
            };
    };

    class LessThan :
        public ComparisonReif
    {
        public:
            inline explicit LessThan(const IntegerVariableID v1, const IntegerVariableID v2) :
                ComparisonReif(v1, v2, +constant_variable(true), true, ComparisonOperator::LessThan)
            {
            };
    };

    class LessThanEqual :
        public ComparisonReif
    {
        public:
            inline explicit LessThanEqual(const IntegerVariableID v1, const IntegerVariableID v2) :
                ComparisonReif(v1, v2, +constant_variable(true), true, ComparisonOperator::LessThanEqual)
            {
            };
    };
}

#endif
