/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LITERAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LITERAL_HH 1

#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <string>
#include <variant>
#include <vector>

namespace gcs
{
    struct LiteralFromIntegerVariable
    {
        IntegerVariableID var;
        enum { Equal, NotEqual, GreaterEqual, Less } state;
        Integer value;

        [[ nodiscard ]] auto operator<=> (const LiteralFromIntegerVariable &) const = default;
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

        [[ nodiscard ]] auto operator<=> (const LiteralFromBooleanVariable &) const = default;
    };

    [[ nodiscard ]] inline auto operator ! (const BooleanVariableID var) -> LiteralFromBooleanVariable
    {
        return LiteralFromBooleanVariable{ var, LiteralFromBooleanVariable::False };
    }

    [[ nodiscard ]] inline auto operator + (const BooleanVariableID var) -> LiteralFromBooleanVariable
    {
        return LiteralFromBooleanVariable{ var, LiteralFromBooleanVariable::True };
    }

    using Literal = std::variant<LiteralFromIntegerVariable, LiteralFromBooleanVariable>;

    [[ nodiscard ]] auto operator ! (const Literal &) -> Literal;

    [[ nodiscard ]] auto debug_string(const Literal &) -> std::string;

    using Literals = std::vector<Literal>;

    auto sanitise_literals(Literals &) -> void;
}

#endif
