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
        enum class Operator { Equal, NotEqual, GreaterEqual, Less };
        Operator state;
        Integer value;

        [[ nodiscard ]] auto operator<=> (const LiteralFromIntegerVariable &) const = default;
    };

    [[ nodiscard ]] inline auto operator == (const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{ var, LiteralFromIntegerVariable::Operator::Equal, val };
    }

    [[ nodiscard ]] inline auto operator != (const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{ var, LiteralFromIntegerVariable::Operator::NotEqual, val };
    }

    [[ nodiscard ]] inline auto operator < (const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{ var, LiteralFromIntegerVariable::Operator::Less, val };
    }

    [[ nodiscard ]] inline auto operator >= (const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{ var, LiteralFromIntegerVariable::Operator::GreaterEqual, val };
    }

    struct TrueLiteral
    {
        [[ nodiscard ]] auto operator<=> (const TrueLiteral &) const = default;
    };

    struct FalseLiteral
    {
        [[ nodiscard ]] auto operator<=> (const FalseLiteral &) const = default;
    };

    using Literal = std::variant<LiteralFromIntegerVariable, TrueLiteral, FalseLiteral>;

    [[ nodiscard ]] auto is_literally_true(const Literal &) -> bool;

    [[ nodiscard ]] auto is_literally_false(const Literal &) -> bool;

    [[ nodiscard ]] auto operator ! (const Literal &) -> Literal;

    [[ nodiscard ]] auto debug_string(const Literal &) -> std::string;

    using Literals = std::vector<Literal>;

    using WeightedLiterals = std::vector<std::pair<Integer, Literal> >;

    [[ nodiscard ]] auto sanitise_literals(Literals &) -> bool;
}

#endif
