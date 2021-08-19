/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH 1

#include <gcs/constraint.hh>
#include <gcs/literal.hh>
#include <gcs/variable_id.hh>

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

            virtual auto describe_for_proof() -> std::string override;
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

    class EqualsIf :
        public ComparisonReif
    {
        public:
            inline explicit EqualsIf(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
                ComparisonReif(v1, v2, cond, false, ComparisonOperator::Equals)
            {
            };
    };

    class EqualsIff :
        public ComparisonReif
    {
        public:
            inline explicit EqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
                ComparisonReif(v1, v2, cond, true, ComparisonOperator::Equals)
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

    class NotEqualsIff :
        public ComparisonReif
    {
        public:
            inline explicit NotEqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
                ComparisonReif(v1, v2, ! cond, true, ComparisonOperator::Equals)
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

    class GreaterThan :
        public ComparisonReif
    {
        public:
            inline explicit GreaterThan(const IntegerVariableID v1, const IntegerVariableID v2) :
                ComparisonReif(v1, v2, +constant_variable(false), true, ComparisonOperator::LessThanEqual)
            {
            };
    };

    class GreaterThanEqual :
        public ComparisonReif
    {
        public:
            inline explicit GreaterThanEqual(const IntegerVariableID v1, const IntegerVariableID v2) :
                ComparisonReif(v1, v2, +constant_variable(false), true, ComparisonOperator::LessThan)
            {
            };
    };

    class LessThanIff :
        public ComparisonReif
    {
        public:
            inline explicit LessThanIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
                ComparisonReif(v1, v2, cond, true, ComparisonOperator::LessThan)
            {
            };
    };

    class LessThanEqualIff :
        public ComparisonReif
    {
        public:
            inline explicit LessThanEqualIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
                ComparisonReif(v1, v2, cond, true, ComparisonOperator::LessThanEqual)
            {
            };
    };

    class GreaterThanIff :
        public ComparisonReif
    {
        public:
            inline explicit GreaterThanIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
                ComparisonReif(v1, v2, ! cond, true, ComparisonOperator::LessThanEqual)
            {
            };
    };

    class GreaterThanEqualIff :
        public ComparisonReif
    {
        public:
            inline explicit GreaterThanEqualIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
                ComparisonReif(v1, v2, ! cond, true, ComparisonOperator::LessThan)
            {
            };
    };
}

#endif
