#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LITERAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LITERAL_HH

#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <string>
#include <variant>
#include <vector>

namespace gcs
{
    /**
     * \defgroup Literals Literal expressions
     */

    /**
     * \brief A literal, asserting that an IntegerVariableID is equal, not
     * equal, less than, or greater than or equal to an Integer constant.
     *
     * Usually this is created by writing `var == val`, `var != val`, `var <
     * val` or `var >= val`.
     *
     * \ingroup Core
     * \ingroup Literals
     */
    struct LiteralFromIntegerVariable final
    {
        IntegerVariableID var;
        enum class Operator
        {
            Equal,
            NotEqual,
            GreaterEqual,
            Less
        };
        Operator op;
        Integer value;

        /**
         * \brief Comparison, no defined meaning but allows for sorting etc.
         */
        [[nodiscard]] constexpr auto operator<=>(const LiteralFromIntegerVariable &) const = default;
    };

    /**
     * \brief Create a Literal that the specified IntegerVariableID is equal to
     * the specified Value.
     *
     * \ingroup Literals
     * \see LiteralFromIntegerVariable
     */
    [[nodiscard]] constexpr inline auto operator==(const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{var, LiteralFromIntegerVariable::Operator::Equal, val};
    }

    /**
     * \brief Create a Literal that the specified IntegerVariableID is not equal to
     * the specified Value.
     *
     * \ingroup Literals
     * \see LiteralFromIntegerVariable
     */
    [[nodiscard]] constexpr inline auto operator!=(const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{var, LiteralFromIntegerVariable::Operator::NotEqual, val};
    }

    /**
     * \brief Create a Literal that the specified IntegerVariableID is less than
     * the specified Value.
     *
     * \ingroup Literals
     * \see LiteralFromIntegerVariable
     */
    [[nodiscard]] constexpr inline auto operator<(const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{var, LiteralFromIntegerVariable::Operator::Less, val};
    }

    /**
     * \brief Create a Literal that the specified IntegerVariableID is greater
     * than or equal to the specified Value.
     *
     * \ingroup Literals
     * \see LiteralFromIntegerVariable
     */
    [[nodiscard]] constexpr inline auto operator>=(const IntegerVariableID var, const Integer val) -> LiteralFromIntegerVariable
    {
        return LiteralFromIntegerVariable{var, LiteralFromIntegerVariable::Operator::GreaterEqual, val};
    }

    /**
     * \brief A Literal that is always true.
     *
     * \ingroup Literals
     */
    struct TrueLiteral final
    {
        /**
         * \brief Comparison, no defined meaning but allows for sorting etc.
         */
        [[nodiscard]] auto operator<=>(const TrueLiteral &) const = default;
    };

    /**
     * \brief A Literal that is always false.
     *
     * \ingroup Literals
     */
    struct FalseLiteral final
    {
        /**
         * \brief Comparison, no defined meaning but allows for sorting etc.
         */
        [[nodiscard]] constexpr auto operator<=>(const FalseLiteral &) const = default;
    };

    /**
     * \brief A Literal can be a LiteralFromIntegerVariable, or a TrueLiteral or
     * FalseLiteral.
     *
     * \ingroup Literals
     */
    using Literal = std::variant<LiteralFromIntegerVariable, TrueLiteral, FalseLiteral>;

    /**
     * \brief Negate a Literal.
     *
     * Gives the literal with the opposite meaning, for example equals becomes
     * not equal, and TrueLiteral becomes a FalseLiteral.
     *
     * \ingroup Literals
     */
    [[nodiscard]] auto operator!(const Literal &) -> Literal;

    /**
     * \brief Negate a LiteralFromIntegerVariable.
     *
     * Gives the literal with the opposite meaning, for example equals becomes
     * not equal.
     *
     * \ingroup Literals
     */
    [[nodiscard]] auto operator!(const LiteralFromIntegerVariable &) -> LiteralFromIntegerVariable;

    /**
     * \brief A vector of Literal values.
     *
     * \ingroup Literals
     */
    using Literals = std::vector<Literal>;
}

#endif
