/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LINEAR_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LINEAR_UTILS_HH

#include <gcs/innards/proof-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/linear.hh>

#include <optional>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief A SimpleIntegerVariableID, together with a multiplication
     * coefficient.
     *
     * \ingroup Innards
     */
    using CoefficientAndSimpleVariable = std::pair<Integer, SimpleIntegerVariableID>;

    /**
     * \brief A Linear that only uses SimpleIntegerVariableID terms.
     *
     * \ingroup Innards
     * \sa SanitisedLinear
     * \sa gcs::innards::sanitise_linear()
     * \sa gcs::innards::propagate_linear()
     */
    using SimpleLinear = std::vector<CoefficientAndSimpleVariable>;

    /**
     * \brief A SimpleIntegerVariableID, with a coefficient that is either one
     * if true, or negative one if false.
     *
     * \ingroup Innards
     */
    using IsPositiveAndSimpleVariable = std::pair<bool, SimpleIntegerVariableID>;

    /**
     * \brief A Linear where the coefficients are all either one or minus one,
     * and using only SimpleIntegerVariableID terms.
     *
     * \ingroup Innards
     * \sa SanitisedLinear
     * \sa gcs::innards::sanitise_linear()
     * \sa gcs::innards::propagate_sum()
     */
    using SimpleSum = std::vector<IsPositiveAndSimpleVariable>;

    /**
     * \brief A Linear where all the coefficients are one and using only
     * SimpleIntegerVariableID terms.
     *
     * \ingroup Innards
     * \sa SanitisedLinear
     * \sa gcs::innards::sanitise_linear()
     * \sa gcs::innards::propagate_sum_all_positive()
     */
    using SimpleIntegerVariableIDs = std::vector<SimpleIntegerVariableID>;

    /**
     * \brief A Linear with its complicated bits removed.
     *
     * \sa gcs::innards::sanitise_linear()
     */
    using SanitisedLinear = std::variant<SimpleIntegerVariableIDs, SimpleSum, SimpleLinear>;

    /**
     * \brief Sanitise a linear equation.
     *
     * Figures out whether a linear equation falls into one of the simpler cases
     * of being a sum, possibly with negatives. This also calls
     * gcs::simplify_linear().
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto sanitise_linear(const Linear &) -> std::pair<SanitisedLinear, Integer>;

    /**
     * \brief Simplify a linear equation.
     *
     * Deals with constants, groups liked variables, removes zero coefficients,
     * etc. The second value in the return should be added to the right hand
     * side of the equation or inequality.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto simplify_linear(const Linear &) -> std::pair<SimpleLinear, Integer>;

    /**
     * \brief Propagate a linear equality or inequality.
     *
     * \ingroup Innards
     */
    auto propagate_linear(const SimpleLinear &, Integer, State &, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;

    /**
     * \brief Propagate a simple sum equality or inequality.
     *
     * \ingroup Innards
     */
    auto propagate_sum(const SimpleSum &, Integer, State &, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;

    /**
     * \brief Propagate an all-positive sum equality or inequality.
     *
     * \ingroup Innards
     */
    auto propagate_sum_all_positive(const SimpleIntegerVariableIDs &, Integer, State &, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;
}

#endif
