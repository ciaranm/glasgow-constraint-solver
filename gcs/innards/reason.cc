#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::generic_reason(const State & state, const std::vector<IntegerVariableID> & vars,
    const std::optional<Literal> & extra_lit) -> ReasonFunction
{
    Reason reason;
    for (const auto & var : vars) {
        auto bounds = state.bounds(var);
        if (bounds.first == bounds.second)
            reason.push_back(var == bounds.first);
        else {
            reason.push_back(var >= bounds.first);
            reason.push_back(var <= bounds.second);
            if (state.domain_has_holes(var)) {
                for (auto v = bounds.first + 1_i; v < bounds.second; ++v)
                    if (! state.in_domain(var, v))
                        reason.push_back(var != v);
            }
        }
    }
    if (extra_lit)
        reason.push_back(*extra_lit);

    return [=]() { return reason; };
}

auto gcs::innards::bounds_reason(const State & state, const std::vector<IntegerVariableID> & vars,
    const std::optional<Literal> & extra_lit) -> ReasonFunction
{
    Reason reason;
    for (const auto & var : vars) {
        auto bounds = state.bounds(var);
        if (bounds.first == bounds.second)
            reason.push_back(var == bounds.first);
        else {
            reason.push_back(var >= bounds.first);
            reason.push_back(var <= bounds.second);
        }
    }
    if (extra_lit)
        reason.push_back(*extra_lit);

    return [=]() { return reason; };
}

auto innards::singleton_reason(const ProofLiteralOrFlag & lit) -> ReasonFunction
{
    Reason reason;
    reason.push_back(lit);
    return [=]() { return reason; };
}
