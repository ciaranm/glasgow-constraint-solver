#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_CONDITION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_CONDITION_HH

#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

namespace gcs
{
    /**
     * \brief The operator used by a VariableCondition.
     *
     * \see IntegerVariableCondition
     */
    enum class VariableConditionOperator
    {
        Equal,
        NotEqual,
        GreaterEqual,
        Less
    };

    /**
     * \brief A variable condition, asserting that an IntegerVariableID or other
     * variable type is equal, not equal, less than, or greater than or equal to
     * an Integer constant.
     *
     * Usually this is created by writing `var == val`, `var != val`, `var <
     * val` or `var >= val`.
     *
     * \ingroup Core
     */
    template <typename VariableType_>
    struct VariableConditionFrom final
    {
        VariableType_ var;
        VariableConditionOperator op;
        Integer value;

        /**
         * \brief Comparison, no defined meaning but allows for sorting etc.
         */
        [[nodiscard]] constexpr auto operator<=>(const VariableConditionFrom<VariableType_> &) const = default;
    };

    using IntegerVariableCondition = VariableConditionFrom<IntegerVariableID>;

    /**
     * \brief Create an IntegerVariableCondition that the specified IntegerVariableID is equal to
     * the specified Value.
     *
     * \ingroup Literals
     * \see IntegerVariableCondition
     */
    [[nodiscard]] constexpr inline auto operator==(const IntegerVariableID var, const Integer val) -> IntegerVariableCondition
    {
        return IntegerVariableCondition{var, VariableConditionOperator::Equal, val};
    }

    /**
     * \brief Create an IntegerVariableCondition that the specified IntegerVariableID is not equal to
     * the specified Value.
     *
     * \ingroup Literals
     * \see IntegerVariableCondition
     */
    [[nodiscard]] constexpr inline auto operator!=(const IntegerVariableID var, const Integer val) -> IntegerVariableCondition
    {
        return IntegerVariableCondition{var, VariableConditionOperator::NotEqual, val};
    }

    /**
     * \brief Create an IntegerVariableCondition that the specified IntegerVariableID is less than
     * the specified Value.
     *
     * \ingroup Literals
     * \see IntegerVariableCondition
     */
    [[nodiscard]] constexpr inline auto operator<(const IntegerVariableID var, const Integer val) -> IntegerVariableCondition
    {
        return IntegerVariableCondition{var, VariableConditionOperator::Less, val};
    }

    /**
     * \brief Create an IntegerVariableCondition that the specified IntegerVariableID is greater
     * than or equal to the specified Value.
     *
     * \ingroup Literals
     * \see IntegerVariableCondition
     */
    [[nodiscard]] constexpr inline auto operator>=(const IntegerVariableID var, const Integer val) -> IntegerVariableCondition
    {
        return IntegerVariableCondition{var, VariableConditionOperator::GreaterEqual, val};
    }

    /**
     * \brief Negate an IntegerVariableCondition.
     *
     * Gives the literal with the opposite meaning, for example equals becomes
     * not equal.
     */
    [[nodiscard]] auto operator!(const IntegerVariableCondition &) -> IntegerVariableCondition;
}

#endif
