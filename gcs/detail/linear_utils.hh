/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_DETAIL_LINEAR_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_DETAIL_LINEAR_UTILS_HH

#include <gcs/detail/proof-fwd.hh>
#include <gcs/detail/propagators-fwd.hh>
#include <gcs/detail/state-fwd.hh>
#include <gcs/linear.hh>

#include <optional>
#include <variant>
#include <vector>

namespace gcs
{
    using CoefficientAndSimpleVariable = std::pair<Integer, SimpleIntegerVariableID>;
    using SimpleLinear = std::vector<CoefficientAndSimpleVariable>;

    using IsPositiveAndSimpleVariable = std::pair<bool, SimpleIntegerVariableID>;
    using SimpleSum = std::vector<IsPositiveAndSimpleVariable>;

    using SimpleIntegerVariableIDs = std::vector<SimpleIntegerVariableID>;

    using SanitisedLinear = std::variant<SimpleIntegerVariableIDs, SimpleSum, SimpleLinear>;

    [[nodiscard]] auto sanitise_linear(const Linear &) -> std::pair<SanitisedLinear, Integer>;

    [[nodiscard]] auto simplify_linear(const Linear &) -> std::pair<SimpleLinear, Integer>;

    auto propagate_linear(const SimpleLinear &, Integer, State &, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;

    auto propagate_sum(const SimpleSum &, Integer, State &, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;

    auto propagate_sum_all_positive(const SimpleIntegerVariableIDs &, Integer, State &, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;
}

#endif
