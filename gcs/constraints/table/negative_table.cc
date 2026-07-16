#include <gcs/constraints/table/hints.hh>
#include <gcs/constraints/table/negative_table.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <optional>
#include <sstream>
#include <type_traits>
#include <utility>
#include <variant>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::nullopt;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique;
using std::unique_ptr;
using std::variant;
using std::vector;
using std::visit;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

namespace
{
    template <typename T_>
    auto depointinate(const ArrayParam<T_> & t) -> const T_ &
    {
        return *t;
    }

    auto tuple_entry_as_string(Integer i) -> string
    {
        return i.to_string();
    }

    auto tuple_entry_as_string(Wildcard) -> string
    {
        return "*";
    }

    auto tuple_entry_as_string(const variant<Integer, Wildcard> & v) -> string
    {
        return visit([](auto v) { return tuple_entry_as_string(v); }, v);
    }

    auto add_literal(Literals & lits, const IntegerVariableID & var, const Integer & val)
    {
        lits.emplace_back(var != val);
    }

    auto add_literal(Literals &, const IntegerVariableID &, const Wildcard &)
    {
    }

    auto add_literal(Literals & lits, const IntegerVariableID & var, const IntegerOrWildcard & val)
    {
        visit([&](const auto & val) { add_literal(lits, var, val); }, val);
    }

    auto operator==(const IntegerVariableID &, const Wildcard &) -> Literal
    {
        return TrueLiteral{};
    }

    auto operator==(const IntegerVariableID & v, const IntegerOrWildcard & val) -> Literal
    {
        return visit([&](const auto & val) -> Literal { return v == val; }, val);
    }

    auto operator!=(const IntegerVariableID &, const Wildcard &) -> Literal
    {
        return FalseLiteral{};
    }

    auto operator!=(const IntegerVariableID & v, const IntegerOrWildcard & val) -> Literal
    {
        return visit([&](const auto & val) -> Literal { return v != val; }, val);
    }
}

namespace gcs
{
    using ::operator==;
    using ::operator!=;
}

NegativeTable::NegativeTable(vector<IntegerVariableID> v, ExtensionalTuples t) : _vars(move(v)), _tuples(move(t))
{
}

auto NegativeTable::clone() const -> unique_ptr<Constraint>
{
    return make_unique<NegativeTable>(_vars, ExtensionalTuples{_tuples});
}

auto NegativeTable::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto NegativeTable::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    visit(
        [&](auto & tuples) {
            for (auto & tuple : depointinate(tuples))
                if (tuple.size() != _vars.size())
                    throw InvalidProblemDefinitionException{"table size mismatch"};
        },
        _tuples);
    return true;
}

auto NegativeTable::define_proof_model(ProofModel & model) -> void
{
    visit(
        [&](auto & tuples) {
            for (auto & t : depointinate(tuples)) {
                Literals lits;
                for (const auto & [idx, v] : enumerate(_vars))
                    add_literal(lits, v, t[idx]);
                model.add_constraint(move(lits));
            }
        },
        _tuples);
}

namespace
{
    constexpr size_t no_watch = std::numeric_limits<size_t>::max();

    // Root-level detection, run once in the initialiser: mirrors the coarse
    // initialiser but keeps NO persistent bookkeeping (the two watches are armed
    // later, in the propagator's first un-fired run). This catches a tuple already
    // violated or unit against the initial domains before search starts, so the
    // search tree matches the coarse path. Hoisted into a named template for the
    // same MSVC-C1001 reason as the propagator body below.
    template <typename Vars_, typename Tuples_, typename Owner_, typename Inference_>
    auto detect_root_negative_table(const Vars_ & vars, const Tuples_ & tuples, const Owner_ & owner, const Reason & reason, const State & state,
        Inference_ & inference, ProofLogger * const logger) -> void
    {
        const auto & tuple_data = depointinate(tuples);
        for (size_t ti = 0; ti < tuple_data.size(); ++ti) {
            const auto & t = tuple_data[ti];

            auto find_unbroken = [&](size_t skip) -> optional<size_t> {
                for (size_t p = 0; p < vars.size(); ++p) {
                    if (p == skip)
                        continue;
                    if (state.test_literal(vars[p] == t[p]) != LiteralIs::DefinitelyTrue)
                        return p;
                }
                return nullopt;
            };

            auto w1 = find_unbroken(no_watch);
            if (! w1)
                inference.contradiction(logger, JustifyUsingRUP{hints::NegativeTable{owner}}, reason);
            auto w2 = find_unbroken(*w1);
            if (! w2)
                inference.infer(logger, vars[*w1] != t[*w1], JustifyUsingRUP{hints::NegativeTable{owner}}, reason);
        }
    }

    // The refined-watch negative-table propagator. A forbidden tuple t is the clause
    // (vars[0] != t[0]) v ... v (vars[n-1] != t[n-1]); it is violated iff every
    // vars[p] == t[p] holds ("broken" == that equality is DefinitelyTrue, which also
    // captures a wildcard position, whose == overloads to TrueLiteral). We keep two
    // watches per tuple on not-broken positions; when a watched vars[p] == t[p]
    // becomes entailed the watch fires and we move it, and with only one not-broken
    // position left we force its survivor's negation, or clash. This is exactly the
    // two-watched-literal scheme of install_refined_nogoods (nogoods.cc): the two
    // packed watch positions live in ctx.watch_state, restored in lockstep with the
    // watches, and the unit case just infers and leaves the consumed watch to be
    // restored on backtrack. Hoisted into a named template for the MSVC-C1001 reason
    // noted above (a generic-on-inference lambda nesting further lambdas).
    template <typename Vars_, typename Tuples_, typename SetUp_, typename Owner_, typename Inference_>
    auto propagate_negative_table_refined(const Vars_ & vars, const Tuples_ & tuples, const SetUp_ & set_up, const Owner_ & owner,
        const Reason & reason, const State & state, Inference_ & inference, ProofLogger * const logger, const RefinedWatchContext & ctx)
        -> PropagatorState
    {
        const auto & tuple_data = depointinate(tuples);
        auto pack = [](size_t a, size_t b) -> std::uint64_t { return (static_cast<std::uint64_t>(a) << 32) | static_cast<std::uint32_t>(b); };

        // A not-broken position other than skip1/skip2 to place a watch on. A
        // DefinitelyFalse position counts as not-broken -- a satisfied clause may
        // rest a watch on it.
        auto find_unbroken = [&](const auto & t, size_t skip1, size_t skip2) -> optional<size_t> {
            for (size_t p = 0; p < vars.size(); ++p) {
                if (p == skip1 || p == skip2)
                    continue;
                if (state.test_literal(vars[p] == t[p]) != LiteralIs::DefinitelyTrue)
                    return p;
            }
            return nullopt;
        };

        if (ctx.fired_payloads().empty()) {
            // First (root) run -- the only time this propagator runs un-fired: arm two
            // watches for every tuple not yet set up (all of them, once). This arming
            // lives in the persistent root epoch, so the non-backtrackable set_up
            // counter stays in step with the restored watches across restarts.
            for (size_t ti = *set_up; ti < tuple_data.size(); ++ti) {
                const auto & t = tuple_data[ti];
                auto key = static_cast<std::uint32_t>(ti);
                auto w1 = find_unbroken(t, no_watch, no_watch);
                if (! w1)
                    inference.contradiction(logger, JustifyUsingRUP{hints::NegativeTable{owner}}, reason);
                auto w2 = find_unbroken(t, *w1, no_watch);
                if (! w2) {
                    inference.infer(logger, vars[*w1] != t[*w1], JustifyUsingRUP{hints::NegativeTable{owner}}, reason);
                    ctx.watch(vars[*w1] == t[*w1], key);
                    ctx.set_watch_state(key, pack(*w1, *w1));
                }
                else {
                    ctx.watch(vars[*w1] == t[*w1], key);
                    ctx.watch(vars[*w2] == t[*w2], key);
                    ctx.set_watch_state(key, pack(*w1, *w2));
                }
            }
            *set_up = tuple_data.size();
            return PropagatorState::Enable;
        }

        // Visit each tuple that had a watch fire this wake, once.
        vector<size_t> fired;
        for (auto payload : ctx.fired_payloads())
            fired.push_back(payload);
        sort(fired);
        fired.erase(unique(fired.begin(), fired.end()), fired.end());

        auto is_broken = [&](const auto & t, size_t p) { return state.test_literal(vars[p] == t[p]) == LiteralIs::DefinitelyTrue; };

        for (size_t ti : fired) {
            const auto & t = tuple_data[ti];
            auto key = static_cast<std::uint32_t>(ti);
            auto packed = ctx.watch_state(key);
            size_t p = static_cast<size_t>(packed >> 32), q = static_cast<size_t>(packed & 0xffffffffu);

            bool b1 = is_broken(t, p), b2 = is_broken(t, q);
            if (! b1 && ! b2)
                continue; // a spurious re-fire on an already-handled tuple

            if (b1 && b2) {
                // Both watched literals entailed (both consumed). Find two fresh
                // not-broken positions; one short means unit, none means clash.
                auto new1 = find_unbroken(t, no_watch, no_watch);
                if (! new1)
                    inference.contradiction(logger, JustifyUsingRUP{hints::NegativeTable{owner}}, reason);
                auto new2 = find_unbroken(t, *new1, no_watch);
                if (! new2)
                    // Unit: infer; both consumed watches are restored on backtrack,
                    // so leave watch_state at (p, q) to match them.
                    inference.infer(logger, vars[*new1] != t[*new1], JustifyUsingRUP{hints::NegativeTable{owner}}, reason);
                else {
                    ctx.watch(vars[*new1] == t[*new1], key);
                    ctx.watch(vars[*new2] == t[*new2], key);
                    ctx.set_watch_state(key, pack(*new1, *new2));
                }
            }
            else if (b1) {
                // Watch at p fired (consumed); q still armed. Move p, or unit on q.
                auto new1 = find_unbroken(t, q, no_watch);
                if (! new1)
                    inference.infer(logger, vars[q] != t[q], JustifyUsingRUP{hints::NegativeTable{owner}}, reason);
                else {
                    ctx.watch(vars[*new1] == t[*new1], key);
                    ctx.set_watch_state(key, pack(*new1, q));
                }
            }
            else {
                // Watch at q fired (consumed); p still armed. Move q, or unit on p.
                auto new2 = find_unbroken(t, p, no_watch);
                if (! new2)
                    inference.infer(logger, vars[p] != t[p], JustifyUsingRUP{hints::NegativeTable{owner}}, reason);
                else {
                    ctx.watch(vars[*new2] == t[*new2], key);
                    ctx.set_watch_state(key, pack(p, *new2));
                }
            }
        }
        return PropagatorState::Enable;
    }
}

auto NegativeTable::install_propagators(Propagators & propagators) -> void
{
    // High-water mark of tuples whose two watches have been armed. Advanced once, in
    // the propagator's first (root) run; non-backtrackable, but the arming lives in
    // the persistent root epoch, so it stays in step with the restored watches. (For
    // this static tuple set it just goes 0 -> size once; the counter matters only so
    // a restart-root re-propagation does not re-arm.)
    auto set_up = make_shared<size_t>(0);

    // The reason ranges over the fixed variable scope, so build it once here and
    // share it between the initialiser and the propagator rather than rebuilding
    // it on every wake (see dev_docs/propagator-performance.md).
    auto table_reason = generic_reason(_vars);

    visit(
        [&, this](auto && tuples) {
            // Detect a root-level contradiction or unit before search starts (identical
            // search tree), discarding bookkeeping. A position is unusable as a watch
            // iff `var == t[pos]` is DefinitelyTrue — this captures both "var is forced
            // to t[pos]" and "t[pos] is a wildcard" (`var == Wildcard` overloads to
            // TrueLiteral, which tests DefinitelyTrue).
            propagators.install_initialiser(
                [vars = _vars, tuples = tuples, owner = constraint_id(), reason = table_reason](const State & state, auto & inference,
                    ProofLogger * const logger) -> void { detect_root_negative_table(vars, tuples, owner, reason, state, inference, logger); });

            // Refined per-literal watches instead of a coarse on_change over the whole
            // scope: each tuple arms two watches and is revisited only when one fires,
            // so a wake touches just the affected tuples rather than rescanning all.
            //
            // The variables are still declared as the propagator's scope, via
            // on_instantiated triggers, so degree-based branchers (dom_then_deg,
            // dom-wdeg) see this constraint on its variables exactly as the coarse
            // version did -- a watch-only (empty-Triggers) propagator is otherwise
            // invisible to those heuristics and perturbs the search. on_instantiated is
            // the least-frequent coarse trigger, and after the one-off setup every such
            // wake finds fired-payloads empty and the tuples already armed, so it is an
            // O(1) no-op: the real work still happens only on watch fires.
            Triggers scope_triggers;
            for (auto & v : _vars)
                scope_triggers.on_instantiated.emplace_back(v);

            propagators.install(
                constraint_id(),
                [vars = move(_vars), tuples = move(tuples), set_up = set_up, owner = constraint_id(), reason = std::move(table_reason)](
                    const State & state, auto & inference, ProofLogger * const logger, const RefinedWatchContext & ctx) -> PropagatorState {
                    return propagate_negative_table_refined(vars, tuples, set_up, owner, reason, state, inference, logger, ctx);
                },
                std::move(scope_triggers));
        },
        _tuples);
}

auto NegativeTable::constraint_type() const -> std::string
{
    return "negative_table";
}

auto NegativeTable::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> tuple_terms;
    visit(
        [&](const auto & tuples) {
            for (const auto & t : depointinate(tuples)) {
                vector<SExpr> row;
                for (const auto & v : t)
                    row.push_back(SExpr::atom(tuple_entry_as_string(v)));
                tuple_terms.push_back(SExpr::list(std::move(row)));
            }
        },
        _tuples);
    vector<SExpr> vars;
    for (const auto & var : _vars)
        vars.push_back(tracker.s_expr_term_of(var));
    return SExpr::list(
        {SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(tuple_terms)), SExpr::list(std::move(vars))});
}
