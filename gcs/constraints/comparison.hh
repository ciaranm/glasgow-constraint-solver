/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH

#include <gcs/constraint.hh>
#include <gcs/literal.hh>
#include <gcs/variable_id.hh>

namespace gcs
{
    class CompareLessThanReif : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;
        Literal _cond;
        bool _full_reif;
        bool _or_equal;

    public:
        explicit CompareLessThanReif(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond, bool full_reif, bool or_equal);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(detail::Propagators &, const detail::State &) && -> void override;
    };

    class LessThan : public CompareLessThanReif
    {
    public:
        inline explicit LessThan(const IntegerVariableID v1, const IntegerVariableID v2) :
            CompareLessThanReif(v1, v2, TrueLiteral{}, true, false){};
    };

    class LessThanIf : public CompareLessThanReif
    {
    public:
        inline explicit LessThanIf(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            CompareLessThanReif(v1, v2, cond, false, false){};
    };

    class LessThanEqual : public CompareLessThanReif
    {
    public:
        inline explicit LessThanEqual(const IntegerVariableID v1, const IntegerVariableID v2) :
            CompareLessThanReif(v1, v2, TrueLiteral{}, true, true){};
    };

    class GreaterThan : public CompareLessThanReif
    {
    public:
        inline explicit GreaterThan(const IntegerVariableID v1, const IntegerVariableID v2) :
            CompareLessThanReif(v2, v1, TrueLiteral{}, true, false){};
    };

    class GreaterThanEqual : public CompareLessThanReif
    {
    public:
        inline explicit GreaterThanEqual(const IntegerVariableID v1, const IntegerVariableID v2) :
            CompareLessThanReif(v2, v1, TrueLiteral{}, true, true){};
    };

    class LessThanIff : public CompareLessThanReif
    {
    public:
        inline explicit LessThanIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            CompareLessThanReif(v1, v2, cond, true, false){};
    };

    class LessThanEqualIff : public CompareLessThanReif
    {
    public:
        inline explicit LessThanEqualIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            CompareLessThanReif(v1, v2, cond, true, true){};
    };

    class GreaterThanIff : public CompareLessThanReif
    {
    public:
        inline explicit GreaterThanIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            CompareLessThanReif(v2, v1, cond, true, false){};
    };

    class GreaterThanEqualIff : public CompareLessThanReif
    {
    public:
        inline explicit GreaterThanEqualIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            CompareLessThanReif(v2, v1, cond, true, true){};
    };
}

#endif
