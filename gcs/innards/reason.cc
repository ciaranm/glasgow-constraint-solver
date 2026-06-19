#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::generic_reason(const State & state, const std::vector<IntegerVariableID> & vars,
    const std::optional<Literal> & extra_lit) -> ReasonFunction
{
    ReasonLiterals reason;
    for (const auto & var : vars) {
        auto bounds = state.bounds(var);
        if (bounds.first == bounds.second)
            reason.push_back(var == bounds.first);
        else {
            reason.push_back(var >= bounds.first);
            reason.push_back(var <= bounds.second);
            if (state.domain_has_holes(var)) {
                // Each maximal run of missing values is one range condition;
                // views take the per-value fallback, since folding views into
                // the interval machinery is deferred.
                if (std::holds_alternative<SimpleIntegerVariableID>(var)) {
                    std::optional<std::pair<Integer, Integer>> run;
                    auto flush = [&]() {
                        if (run) {
                            reason.push_back(not_in_range(var, run->first, run->second));
                            run.reset();
                        }
                    };
                    for (auto v = bounds.first + 1_i; v < bounds.second; ++v) {
                        if (state.in_domain(var, v))
                            flush();
                        else if (run)
                            run->second = v;
                        else
                            run = std::pair{v, v};
                    }
                    flush();
                }
                else {
                    for (auto v = bounds.first + 1_i; v < bounds.second; ++v)
                        if (! state.in_domain(var, v))
                            reason.push_back(var != v);
                }
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
    ReasonLiterals reason;
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
    ReasonLiterals reason;
    reason.push_back(lit);
    return [=]() { return reason; };
}
