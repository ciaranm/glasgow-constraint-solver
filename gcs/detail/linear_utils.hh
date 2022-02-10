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

    [[nodiscard]] auto sanitise_linear(const Linear &) -> std::pair<std::variant<SimpleSum, SimpleLinear>, Integer>;

    auto propagate_linear(const SimpleLinear &, Integer, State &, bool equality,
        std::optional<ProofLine> proof_line) -> std::pair<Inference, PropagatorState>;

    auto propagate_sum(const SimpleSum &, Integer, State &, bool equality,
        std::optional<ProofLine> proof_line) -> std::pair<Inference, PropagatorState>;
}

#endif
