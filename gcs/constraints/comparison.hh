/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH

#include <gcs/constraint.hh>
#include <gcs/literal.hh>
#include <gcs/variable_id.hh>

namespace gcs
{
    enum class ComparisonOperator
    {
        LessThan,
        LessThanEqual
    };

    class ComparisonReif : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;
        Literal _cond;
        bool _full_reif;
        ComparisonOperator _op;

        auto _install_less_than(Propagators &, const State &, bool equal) && -> void;

    public:
        explicit ComparisonReif(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond, bool full_reif, ComparisonOperator op);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(Propagators &, const State &) && -> void override;
    };

    class LessThan : public ComparisonReif
    {
    public:
        inline explicit LessThan(const IntegerVariableID v1, const IntegerVariableID v2) :
            ComparisonReif(v1, v2, TrueLiteral{}, true, ComparisonOperator::LessThan){};
    };

    class LessThanIf : public ComparisonReif
    {
    public:
        inline explicit LessThanIf(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            ComparisonReif(v1, v2, cond, false, ComparisonOperator::LessThan){};
    };

    class LessThanEqual : public ComparisonReif
    {
    public:
        inline explicit LessThanEqual(const IntegerVariableID v1, const IntegerVariableID v2) :
            ComparisonReif(v1, v2, TrueLiteral{}, true, ComparisonOperator::LessThanEqual){};
    };

    class GreaterThan : public ComparisonReif
    {
    public:
        inline explicit GreaterThan(const IntegerVariableID v1, const IntegerVariableID v2) :
            ComparisonReif(v2, v1, TrueLiteral{}, true, ComparisonOperator::LessThan){};
    };

    class GreaterThanEqual : public ComparisonReif
    {
    public:
        inline explicit GreaterThanEqual(const IntegerVariableID v1, const IntegerVariableID v2) :
            ComparisonReif(v2, v1, TrueLiteral{}, true, ComparisonOperator::LessThanEqual){};
    };

    class LessThanIff : public ComparisonReif
    {
    public:
        inline explicit LessThanIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            ComparisonReif(v1, v2, cond, true, ComparisonOperator::LessThan){};
    };

    class LessThanEqualIff : public ComparisonReif
    {
    public:
        inline explicit LessThanEqualIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            ComparisonReif(v1, v2, cond, true, ComparisonOperator::LessThanEqual){};
    };

    class GreaterThanIff : public ComparisonReif
    {
    public:
        inline explicit GreaterThanIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            ComparisonReif(v2, v1, cond, true, ComparisonOperator::LessThan){};
    };

    class GreaterThanEqualIff : public ComparisonReif
    {
    public:
        inline explicit GreaterThanEqualIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            ComparisonReif(v2, v1, cond, true, ComparisonOperator::LessThanEqual){};
    };
}

#endif
