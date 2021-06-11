/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LITERAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LITERAL_HH 1

#include <gcs/integer.hh>
#include <gcs/integer_variable.hh>
#include <gcs/boolean_variable.hh>

#include <variant>

namespace gcs
{
    struct LiteralFromIntegerVariable
    {
        IntegerVariableID var;
        enum { Equal, NotEqual, GreaterEqual, Less } state;
        Integer value;
    };

    [[ nodiscard ]] inline auto operator == (const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{ var, LiteralFromIntegerVariable::Equal, val };
    }

    [[ nodiscard ]] inline auto operator != (const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{ var, LiteralFromIntegerVariable::NotEqual, val };
    }

    [[ nodiscard ]] inline auto operator < (const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{ var, LiteralFromIntegerVariable::Less, val };
    }

    [[ nodiscard ]] inline auto operator >= (const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{ var, LiteralFromIntegerVariable::GreaterEqual, val };
    }

    struct LiteralFromBooleanVariable
    {
        BooleanVariableID var;
        enum { True, False } state;
    };

    using Literal = std::variant<LiteralFromIntegerVariable, LiteralFromBooleanVariable>;
}

#endif
