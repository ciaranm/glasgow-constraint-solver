#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;

namespace
{
    // Walk every value in each variable's domain (lower bound, upper bound, and
    // any holes), appending the facts to `reason`. This is the materialisation
    // of GenericReasonOver.
    auto materialise_generic(const State & state, const std::vector<IntegerVariableID> & vars,
        const optional<Literal> & extra, ReasonLiterals & reason) -> void
    {
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
                        optional<pair<Integer, Integer>> run;
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
                                run = pair{v, v};
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
        if (extra)
            reason.push_back(*extra);
    }

    // Walk only the lower and upper bound of each variable. This is the
    // materialisation of BothBoundsReasonOver.
    auto materialise_bounds(const State & state, const std::vector<IntegerVariableID> & vars,
        const optional<Literal> & extra, ReasonLiterals & reason) -> void
    {
        for (const auto & var : vars) {
            auto bounds = state.bounds(var);
            if (bounds.first == bounds.second)
                reason.push_back(var == bounds.first);
            else {
                reason.push_back(var >= bounds.first);
                reason.push_back(var <= bounds.second);
            }
        }
        if (extra)
            reason.push_back(*extra);
    }

    // Materialisation of ExactSingleValue: `extra` (if any) first, then `var ==
    // value` for each variable, where value is the variable's single current
    // value. The leading-extra order matches the legacy explicit reasons this
    // replaces, keeping proofs byte-identical. Each var must be instantiated.
    auto materialise_exact_single_value(const State & state, const std::vector<IntegerVariableID> & vars,
        const optional<Literal> & extra, ReasonLiterals & reason) -> void
    {
        if (extra)
            reason.push_back(*extra);
        for (const auto & var : vars)
            reason.push_back(var == state.optional_single_value(var).value());
    }
}

auto gcs::innards::materialise(const Reason & reason, const State & state) -> ReasonLiterals
{
    ReasonLiterals result;
    reason.visit(overloaded{
        [&](const NoReason &) {},
        [&](const ExplicitReason & r) { result = r.literals; },
        [&](const GenericReasonOver & r) { materialise_generic(state, *r.vars, r.extra, result); },
        [&](const BothBoundsReasonOver & r) { materialise_bounds(state, *r.vars, r.extra, result); },
        [&](const ExactSingleValue & r) { materialise_exact_single_value(state, *r.vars, r.extra, result); },
        [&](const LazyReasonOver & r) { r.fn(state, result); },
        [&](const NarrowableGenericReasonOver & r) { materialise_generic(state, *r.vars, r.extra, result); },
        [&](const NarrowableBothBoundsReasonOver & r) { materialise_bounds(state, *r.vars, r.extra, result); },
        [&](const NarrowableLazyReasonOver & r) { r.fn(state, result); }});
    return result;
}

auto gcs::innards::generic_reason(const State &, const std::vector<IntegerVariableID> & vars,
    const optional<Literal> & extra_lit) -> Reason
{
    return GenericReasonOver{ReasonVars{vars}, extra_lit};
}

auto gcs::innards::bounds_reason(const State &, const std::vector<IntegerVariableID> & vars,
    const optional<Literal> & extra_lit) -> Reason
{
    return BothBoundsReasonOver{ReasonVars{vars}, extra_lit};
}

auto gcs::innards::singleton_reason(const ProofLiteralOrFlag & lit) -> Reason
{
    return ExplicitReason{ReasonLiterals{lit}};
}

auto gcs::innards::eager_reason(const Reason & reason, const State & state) -> ReasonLiterals
{
    return materialise(reason, state);
}
