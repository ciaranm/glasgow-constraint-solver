#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <type_traits>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;

namespace
{
    // Walk every value in each variable's domain (lower bound, upper bound, and
    // any holes), appending the facts to `reason`. This is the materialisation
    // of GenericReasonOver.
    auto materialise_generic(const State & state, const std::vector<IntegerVariableID> & vars, ReasonLiterals & reason) -> void
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
    }

    // Walk only the lower and upper bound of each variable. This is the
    // materialisation of BothBoundsReasonOver.
    auto materialise_bounds(const State & state, const std::vector<IntegerVariableID> & vars, ReasonLiterals & reason) -> void
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
    }

    // Materialisation of ExactSingleValue: `var == value` for each variable,
    // where value is the variable's single current value. Each var must be
    // instantiated. Leading/extra literals are composed in via concat().
    auto materialise_exact_single_value(const State & state, const std::vector<IntegerVariableID> & vars, ReasonLiterals & reason) -> void
    {
        for (const auto & var : vars)
            reason.push_back(var == state.optional_single_value(var).value());
    }
}

namespace
{
    // Append a reason's literals to `out` (rather than returning a fresh vector),
    // so a ConcatReason can lay its parts down one after another in order. The
    // leaf materialise_* helpers and the LazyReasonFn contract already append.
    auto append_materialised(const Reason & reason, const State & state, ReasonLiterals & out) -> void
    {
        reason.visit(overloaded{
            [&](const NoReason &) {},                                                                       //
            [&](const ExplicitReason & r) { out.insert(out.end(), r.literals.begin(), r.literals.end()); }, //
            [&](const GenericReasonOver & r) { materialise_generic(state, *r.vars, out); },                 //
            [&](const BothBoundsReasonOver & r) { materialise_bounds(state, *r.vars, out); },               //
            [&](const ExactSingleValue & r) { materialise_exact_single_value(state, *r.vars, out); },       //
            [&](const LazyReasonOver & r) { r.fn(state, out); },                                            //
            [&](const NarrowableGenericReasonOver & r) { materialise_generic(state, *r.vars, out); },       //
            [&](const NarrowableBothBoundsReasonOver & r) { materialise_bounds(state, *r.vars, out); },     //
            [&](const NarrowableLazyReasonOver & r) { r.fn(state, out); },                                  //
            [&](const ConcatReason & r) {
                for (const auto & part : r.parts)
                    append_materialised(part, state, out);
            } //
        });
    }
}

auto gcs::innards::materialise(const Reason & reason, const State & state) -> ReasonLiterals
{
    ReasonLiterals result;
    append_materialised(reason, state, result);
    return result;
}

auto gcs::innards::generic_reason(const std::vector<IntegerVariableID> & vars, const optional<Literal> & extra_lit) -> Reason
{
    return with_extra(GenericReasonOver{ReasonVars{vars}}, extra_lit);
}

auto gcs::innards::bounds_reason(const std::vector<IntegerVariableID> & vars, const optional<Literal> & extra_lit) -> Reason
{
    return with_extra(BothBoundsReasonOver{ReasonVars{vars}}, extra_lit);
}

auto gcs::innards::singleton_reason(const ProofLiteralOrFlag & lit) -> Reason
{
    return ExplicitReason{ReasonLiterals{lit}};
}

auto gcs::innards::with_extra(Reason base, ReasonLiterals extra) -> Reason
{
    // Nothing to add: keep the bare (often deferred, allocation-free) base rather
    // than wrapping it in a heap-backed ConcatReason.
    if (extra.empty())
        return base;

    std::vector<Reason> parts;
    parts.reserve(2);
    parts.push_back(std::move(base));
    parts.push_back(ExplicitReason{std::move(extra)});
    return ConcatReason{std::move(parts)};
}

auto gcs::innards::with_extra(Reason base, const optional<Literal> & extra) -> Reason
{
    if (! extra)
        return base;
    return with_extra(std::move(base), ReasonLiterals{*extra});
}

auto gcs::innards::concat(Reason a, Reason b) -> Reason
{
    // NoReason is the identity, so a single real operand stays flat (no
    // ConcatReason allocation).
    if (a.visit([](const auto & r) { return std::is_same_v<std::decay_t<decltype(r)>, NoReason>; }))
        return b;
    if (b.visit([](const auto & r) { return std::is_same_v<std::decay_t<decltype(r)>, NoReason>; }))
        return a;

    std::vector<Reason> parts;
    parts.reserve(2);
    parts.push_back(std::move(a));
    parts.push_back(std::move(b));
    return ConcatReason{std::move(parts)};
}

auto gcs::innards::eager_reason(const Reason & reason, const State & state) -> ReasonLiterals
{
    return materialise(reason, state);
}
