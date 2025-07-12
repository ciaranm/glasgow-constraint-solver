#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_REASON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_REASON_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/variable_id.hh>

#include <ranges>
#include <variant>
#include <vector>

namespace gcs::innards
{
    struct GreaterEqualLowerBound
    {
        IntegerVariableID var;
    };

    struct LessEqualUpperBound
    {
        IntegerVariableID var;
    };

    struct BothBounds
    {
        IntegerVariableID var;
    };

    struct ExactValuesLost
    {
        IntegerVariableID var;
    };

    using DetailedReasonOutlineItem = std::variant<GreaterEqualLowerBound, LessEqualUpperBound, BothBounds, ExactValuesLost, Literal>;

    using DetailedReasonOutline = std::vector<DetailedReasonOutlineItem>;

    struct NoReason
    {
    };

    struct AllVariablesExactValues
    {
    };

    struct AllVariablesBothBounds
    {
    };

    using ReasonOutline = std::variant<NoReason, AllVariablesExactValues, AllVariablesBothBounds, DetailedReasonOutline>;

    template <typename R_, typename C_>
    auto transform_into_reason_outline(const C_ & c) -> DetailedReasonOutline
    {
        auto r = c | std::ranges::views::transform([](const auto & r) { return R_{r}; });
        return DetailedReasonOutline{r.begin(), r.end()};
    }

    using ExpandedReason = std::vector<Literal>;
}

#endif
