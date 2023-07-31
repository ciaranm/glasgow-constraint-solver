#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LINEAR_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LINEAR_UTILS_HH

#include <gcs/expression.hh>
#include <gcs/innards/proof-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <variant>
#include <vector>

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

    /**
     * \brief Propagate a linear equality or inequality.
     *
     * \ingroup Innards
     */
    auto propagate_linear(const SumOf<Weighted<SimpleIntegerVariableID>> &, Integer, State &, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;

    /**
     * \brief Propagate a simple sum equality or inequality.
     *
     * \ingroup Innards
     */
    auto propagate_sum(const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> &, Integer, State &, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;

    /**
     * \brief Propagate an all-positive sum equality or inequality.
     *
     * \ingroup Innards
     */
    auto propagate_sum_all_positive(const SumOf<SimpleIntegerVariableID> &, Integer, State &, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;
}

#endif
