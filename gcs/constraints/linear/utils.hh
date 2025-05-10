#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_UTILS_HH

#include <gcs/expression.hh>
#include <ostream>

namespace gcs::innards
{
    /**
     * A simpler alternative to `Weighted<Var_>` where the coefficient must be positive
     * or negative one.
     *
     * \sa Weighted
     * \ingroup Innards
     */
    template <typename Var_>
    struct PositiveOrNegative final
    {
        bool positive;
        Var_ variable;

        [[nodiscard]] constexpr auto operator<=>(const PositiveOrNegative<Var_> &) const = default;
    };

    /**
     * A PositiveOrNegative can be written to a `std::ostream` if its variable can be.
     *
     * \sa PositiveOrNegative
     * \ingroup Innards
     */
    template <typename Var_>
    auto operator<<(std::ostream & s, const PositiveOrNegative<Var_> & var) -> std::ostream &
    {
        return s << (var.positive ? "" : "-") << var.variable;
    }

    /**
     * \brief A linear expression with its complicated bits removed.
     *
     * \ingroup Innards
     */
    using TidiedUpLinear = std::variant<
        SumOf<SimpleIntegerVariableID>,
        SumOf<PositiveOrNegative<SimpleIntegerVariableID>>,
        SumOf<Weighted<SimpleIntegerVariableID>>>;

    /**
     * \brief Simplify and classify a linear equation.
     *
     * Figures out whether a linear equation falls into one of the simpler cases
     * of being a sum, possibly with negatives. This also simplifies the
     * equation.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto tidy_up_linear(const WeightedSum &) -> std::pair<TidiedUpLinear, Integer>;

    [[nodiscard]] inline auto get_var(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.variable;
    }

    [[nodiscard]] inline auto get_var(const Weighted<SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.variable;
    }

    [[nodiscard]] inline auto get_var(const SimpleIntegerVariableID & cv) -> SimpleIntegerVariableID
    {
        return cv;
    }

    [[nodiscard]] inline auto get_coeff(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.positive ? 1_i : -1_i;
    }

    [[nodiscard]] inline auto get_coeff(const Weighted<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.coefficient;
    }

    [[nodiscard]] inline auto get_coeff(const SimpleIntegerVariableID &) -> Integer
    {
        return 1_i;
    }
}

#endif
