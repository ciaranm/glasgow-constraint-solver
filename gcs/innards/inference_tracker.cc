#include <gcs/innards/inference_tracker.hh>

using namespace gcs;
using namespace gcs::innards;

auto EagerProofLoggingInferenceTracker::expand(const ReasonOutline & reason) -> ExpandedReason
{
    return overloaded{
        [&](const NoReason &) {
            return ExpandedReason{};
        },
        [&](const AllVariablesExactValues &) {
            return expand(transform_into_reason_outline<ExactValuesLost>(*_all_variables_for_current_propagator));
        },
        [&](const AllVariablesBothBounds &) {
            return expand(transform_into_reason_outline<BothBounds>(*_all_variables_for_current_propagator));
        },
        [&](const DetailedReasonOutline & reason) {
            ExpandedReason expanded;
            for (const DetailedReasonOutlineItem & item : reason) {
                overloaded{
                    [&](const GreaterEqualLowerBound & item) {
                        expanded.push_back(item.var >= _state.lower_bound(item.var));
                    },
                    [&](const LessEqualUpperBound & item) {
                        expanded.push_back(item.var < _state.upper_bound(item.var) + 1_i);
                    },
                    [&](const BothBounds & item) {
                        expanded.push_back(item.var >= _state.lower_bound(item.var));
                        expanded.push_back(item.var < _state.upper_bound(item.var) + 1_i);
                    },
                    [&](const ExactValuesLost & item) {
                        auto bounds = _state.bounds(item.var);
                        expanded.push_back(item.var >= bounds.first);
                        expanded.push_back(item.var < bounds.second + 1_i);
                        if (_state.domain_has_holes(item.var)) {
                            for (auto v = bounds.first + 1_i; v < bounds.second; ++v)
                                if (! _state.in_domain(item.var, v))
                                    expanded.push_back(item.var != v);
                        }
                    },
                    [&](const Literal & lit) {
                        expanded.push_back(lit);
                    }}
                    .visit(item);
            }
            return expanded;
        }}
        .visit(reason);
}
