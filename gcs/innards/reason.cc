#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::generic_reason(const State & state, const std::vector<IntegerVariableID> & vars) -> Reason
{
    Literals reason;
    for (const auto & var : vars) {
        auto bounds = state.bounds(var);
        if (bounds.first == bounds.second)
            reason.push_back(var == bounds.first);
        else {
            reason.push_back(var >= bounds.first);
            reason.push_back(var < bounds.second + 1_i);
            if (state.domain_has_holes(var)) {
                for (auto v = bounds.first + 1_i; v < bounds.second; ++v)
                    if (! state.in_domain(var, v))
                        reason.push_back(var != v);
            }
        }
    }

    return [=]() { return reason; };
}
