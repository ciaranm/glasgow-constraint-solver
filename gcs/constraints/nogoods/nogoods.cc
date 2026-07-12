#include <gcs/constraints/nogoods/nogoods.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::make_unique;
using std::nullopt;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::unique;
using std::unique_ptr;
using std::vector;
using std::ranges::sort;

namespace
{
    auto add_distinct(vector<IntegerVariableID> & vs, const IntegerVariableID & v) -> void
    {
        if (std::find(vs.begin(), vs.end(), v) == vs.end())
            vs.push_back(v);
    }
}

auto NogoodStore::add(Nogood nogood) -> void
{
    vector<IntegerVariableID> vs;
    for (const auto & lit : nogood)
        add_distinct(vs, lit.var);
    _vars->push_back(move(vs));
    _nogoods->push_back(move(nogood));
}

auto NogoodStore::size() const -> size_t
{
    return _nogoods->size();
}

Nogoods::Nogoods(vector<Nogood> nogoods, bool refined) : _store(make_shared<NogoodStore>()), _refined(refined)
{
    for (auto & nogood : nogoods) {
        for (const auto & lit : nogood)
            add_distinct(_trigger_vars, lit.var);
        _store->add(move(nogood));
    }
}

Nogoods::Nogoods(shared_ptr<NogoodStore> store, vector<IntegerVariableID> trigger_vars, bool refined) :
    _store(move(store)), _trigger_vars(move(trigger_vars)), _refined(refined)
{
}

auto Nogoods::clone() const -> unique_ptr<Constraint>
{
    // Share the live store; copy the trigger list; preserve the trigger mode.
    return make_unique<Nogoods>(_store, _trigger_vars, _refined);
}

auto Nogoods::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Nogoods::define_proof_model(ProofModel & model) -> void
{
    // A nogood forbids a conjunction of literals, so its definition is the clause
    // of their negations. Only the nogoods present at install are declared here;
    // ones learned later are derived in the proof as they are recorded.
    for (const auto & nogood : *_store->_nogoods) {
        Literals lits;
        for (const auto & lit : nogood)
            lits.emplace_back(! lit);
        model.add_constraint(move(lits));
    }
}

namespace
{
    constexpr size_t no_watch = std::numeric_limits<size_t>::max();

    // Initialise the two watches for nogood `ni`, propagating a unit or raising a
    // contradiction if it is already so. Appends to `watches`, so it must be
    // called with `watches.size() == ni`. Shared between the one-off initialiser
    // and the propagator's lazy catch-up for nogoods learned during search.
    template <typename Inference_>
    auto init_watches_for(size_t ni, const vector<Nogood> & nogoods, const vector<vector<IntegerVariableID>> & nogood_vars,
        vector<pair<size_t, size_t>> & watches, const State & state, Inference_ & inference, ProofLogger * const logger) -> void
    {
        const auto & nogood = nogoods[ni];
        const auto & vars = nogood_vars[ni];

        auto find_unbroken = [&](size_t skip) -> optional<size_t> {
            for (size_t p = 0; p < nogood.size(); ++p) {
                if (p == skip)
                    continue;
                if (state.test_literal(nogood[p]) != LiteralIs::DefinitelyTrue)
                    return p;
            }
            return nullopt;
        };

        auto w1 = find_unbroken(no_watch);
        if (! w1)
            inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(vars));

        auto w2 = find_unbroken(*w1);
        if (! w2) {
            inference.infer(logger, ! nogood[*w1], JustifyUsingRUP{}, generic_reason(vars));
            watches.emplace_back(*w1, *w1);
        }
        else
            watches.emplace_back(*w1, *w2);
    }

    // The coarse path: wake on every change to any nogood variable and re-scan the
    // whole store. Correct but does O(store) work per wake; kept for the growable
    // restart-learning store until that is converted to refined watches (C-2).
    auto install_scan_nogoods(Propagators & propagators, const ConstraintID & id, shared_ptr<vector<Nogood>> nogoods,
        shared_ptr<vector<vector<IntegerVariableID>>> nogood_vars, const vector<IntegerVariableID> & trigger_vars) -> void
    {
        Triggers triggers;
        for (auto & v : trigger_vars)
            triggers.on_change.emplace_back(v);

        // The watches are this propagator's own, non-backtrackable, and grown lazily
        // to keep pace with the nogoods.
        auto watches = make_shared<vector<pair<size_t, size_t>>>();

        // Init: set up watches for the nogoods present up front (none, for a store
        // that the restart loop will grow during search).
        propagators.install_initialiser([nogoods, nogood_vars, watches](const State & state, auto & inference, ProofLogger * const logger) -> void {
            watches->reserve(nogoods->size());
            for (size_t ni = 0; ni < nogoods->size(); ++ni)
                init_watches_for(ni, *nogoods, *nogood_vars, *watches, state, inference, logger);
        });

        propagators.install(
            id,
            [nogoods, nogood_vars, watches](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                // Catch up: initialise watches for any nogoods learned since the last
                // fire. (A unit/contradiction is propagated here, on first sight.)
                for (size_t ni = watches->size(); ni < nogoods->size(); ++ni)
                    init_watches_for(ni, *nogoods, *nogood_vars, *watches, state, inference, logger);

                auto is_broken = [&](const Nogood & nogood, size_t p) -> bool { return state.test_literal(nogood[p]) == LiteralIs::DefinitelyTrue; };

                auto find_unbroken = [&](const Nogood & nogood, size_t skip1, size_t skip2) -> optional<size_t> {
                    for (size_t p = 0; p < nogood.size(); ++p) {
                        if (p == skip1 || p == skip2)
                            continue;
                        if (state.test_literal(nogood[p]) != LiteralIs::DefinitelyTrue)
                            return p;
                    }
                    return nullopt;
                };

                for (size_t ni = 0; ni < nogoods->size(); ++ni) {
                    auto & w = (*watches)[ni];
                    const auto & nogood = (*nogoods)[ni];
                    const auto & vars = (*nogood_vars)[ni];

                    bool b1 = is_broken(nogood, w.first);
                    bool b2 = is_broken(nogood, w.second);

                    if (! b1 && ! b2)
                        continue;

                    if (b1 && b2) {
                        auto new1 = find_unbroken(nogood, no_watch, no_watch);
                        if (! new1)
                            inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(vars));
                        auto new2 = find_unbroken(nogood, *new1, no_watch);
                        if (! new2)
                            inference.infer(logger, ! nogood[*new1], JustifyUsingRUP{}, generic_reason(vars));
                        else {
                            w.first = *new1;
                            w.second = *new2;
                        }
                    }
                    else if (b1) {
                        auto new1 = find_unbroken(nogood, w.second, no_watch);
                        if (! new1)
                            inference.infer(logger, ! nogood[w.second], JustifyUsingRUP{}, generic_reason(vars));
                        else
                            w.first = *new1;
                    }
                    else {
                        auto new2 = find_unbroken(nogood, w.first, no_watch);
                        if (! new2)
                            inference.infer(logger, ! nogood[w.first], JustifyUsingRUP{}, generic_reason(vars));
                        else
                            w.second = *new2;
                    }
                }
                return PropagatorState::Enable;
            },
            triggers);
    }

    // The refined path: a two-watched-literal scheme. Each nogood arms exactly two
    // watches, on two non-entailed literals; when one fires (its literal becomes
    // entailed) the propagator moves it to another non-entailed literal, and if there
    // is none the clause is unit/violated, so it forces the survivor's negation or
    // contradicts. The two watched positions live in per-clause backtrackable scratch
    // (ctx.watch_state, packed), restored in lockstep with the watches, so this
    // bookkeeping never desyncs from the engine across backtrack -- the obstacle that
    // deferred 2WL at stage C-1.
    //
    // Because the watches restore on backtrack, the unit case is trivial: it just
    // infers and leaves the consumed watch to be restored (no need to keep a watch on
    // the falsified literal as classic non-backtrackable SAT 2WL does); and an
    // "abandoned fire" -- a watch consumed in a propagate() that a sibling clause's
    // contradiction ends before this propagator runs -- is undone for free by the
    // following backtrack.
    auto install_refined_nogoods(Propagators & propagators, const ConstraintID & id, shared_ptr<vector<Nogood>> nogoods,
        shared_ptr<vector<vector<IntegerVariableID>>> nogood_vars) -> void
    {
        // Detect any nogood already unit or violated against the initial domains in
        // initialise(), as the coarse path does, so a root-level contradiction is
        // found before search starts (identical search tree). Discards its bookkeeping.
        auto initial_scratch = make_shared<vector<pair<size_t, size_t>>>();
        propagators.install_initialiser(
            [nogoods, nogood_vars, initial_scratch](const State & state, auto & inference, ProofLogger * const logger) -> void {
                initial_scratch->reserve(nogoods->size());
                for (size_t ni = 0; ni < nogoods->size(); ++ni)
                    init_watches_for(ni, *nogoods, *nogood_vars, *initial_scratch, state, inference, logger);
            });

        // High-water mark of nogoods whose two watches have been set up. Catch-up
        // (below) sets up new clauses only at a root re-propagation -- where the
        // restart loop re-enters and where the arming/watch_state edits live in the
        // persistent root epoch (never backtracked between passes) -- so this
        // non-backtrackable counter stays in step with the restored watches.
        auto set_up = make_shared<size_t>(0);

        propagators.install(
            id,
            [nogoods, nogood_vars, set_up](
                const State & state, auto & inference, ProofLogger * const logger, const RefinedWatchContext & ctx) -> PropagatorState {
                auto pack = [](size_t a, size_t b) -> std::uint64_t { return (static_cast<std::uint64_t>(a) << 32) | static_cast<std::uint32_t>(b); };
                // A non-entailed position other than skip1/skip2 to place a watch on.
                // A DefinitelyFalse position counts as non-entailed -- a satisfied
                // clause may rest a watch on it.
                auto find_unbroken = [&](const Nogood & nogood, size_t skip1, size_t skip2) -> optional<size_t> {
                    for (size_t p = 0; p < nogood.size(); ++p) {
                        if (p == skip1 || p == skip2)
                            continue;
                        if (state.test_literal(nogood[p]) != LiteralIs::DefinitelyTrue)
                            return p;
                    }
                    return nullopt;
                };

                if (ctx.fired_payloads().empty()) {
                    // Root re-propagation (the only time this propagator runs un-fired):
                    // set up the two watches for clauses not yet done. For the fixed
                    // store this is all of them, once; for the growable store it is the
                    // nogoods learned since the last pass. A clause already unit/violated
                    // here (e.g. via an initialise-time entailment) is resolved now, as
                    // the firing path never sees those. Thereafter every entailment goes
                    // through requeue and fires a watch, so fired-only suffices.
                    for (size_t ni = *set_up; ni < nogoods->size(); ++ni) {
                        const auto & nogood = (*nogoods)[ni];
                        const auto & vars = (*nogood_vars)[ni];
                        auto w1 = find_unbroken(nogood, no_watch, no_watch);
                        if (! w1)
                            inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(vars));
                        auto w2 = find_unbroken(nogood, *w1, no_watch);
                        if (! w2) {
                            // Unit at first sight: force the negation. The clause is now
                            // satisfied (a root-level fact that persists), so resting a
                            // single watch on the satisfied survivor is enough.
                            inference.infer(logger, ! nogood[*w1], JustifyUsingRUP{}, generic_reason(vars));
                            ctx.watch(nogood[*w1], static_cast<std::uint32_t>(ni));
                            ctx.set_watch_state(static_cast<std::uint32_t>(ni), pack(*w1, *w1));
                        }
                        else {
                            ctx.watch(nogood[*w1], static_cast<std::uint32_t>(ni));
                            ctx.watch(nogood[*w2], static_cast<std::uint32_t>(ni));
                            ctx.set_watch_state(static_cast<std::uint32_t>(ni), pack(*w1, *w2));
                        }
                    }
                    *set_up = nogoods->size();
                    return PropagatorState::Enable;
                }

                // Visit each clause that had a watch fire this wake, once.
                vector<size_t> fired;
                for (auto payload : ctx.fired_payloads())
                    fired.push_back(payload);
                sort(fired);
                fired.erase(unique(fired.begin(), fired.end()), fired.end());

                auto is_broken = [&](const Nogood & nogood, size_t p) { return state.test_literal(nogood[p]) == LiteralIs::DefinitelyTrue; };

                for (size_t ni : fired) {
                    const auto & nogood = (*nogoods)[ni];
                    const auto & vars = (*nogood_vars)[ni];
                    auto packed = ctx.watch_state(static_cast<std::uint32_t>(ni));
                    size_t p = static_cast<size_t>(packed >> 32), q = static_cast<size_t>(packed & 0xffffffffu);

                    bool b1 = is_broken(nogood, p), b2 = is_broken(nogood, q);
                    if (! b1 && ! b2)
                        continue; // a spurious re-fire on an already-handled clause

                    auto key = static_cast<std::uint32_t>(ni);
                    if (b1 && b2) {
                        // Both watched literals entailed (both consumed). Find two fresh
                        // non-entailed literals; one short means unit, none means clash.
                        auto new1 = find_unbroken(nogood, no_watch, no_watch);
                        if (! new1)
                            inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(vars));
                        auto new2 = find_unbroken(nogood, *new1, no_watch);
                        if (! new2)
                            // Unit: infer; both consumed watches are restored on backtrack,
                            // so leave watch_state at (p, q) to match them.
                            inference.infer(logger, ! nogood[*new1], JustifyUsingRUP{}, generic_reason(vars));
                        else {
                            ctx.watch(nogood[*new1], key);
                            ctx.watch(nogood[*new2], key);
                            ctx.set_watch_state(key, pack(*new1, *new2));
                        }
                    }
                    else if (b1) {
                        // Watch at p fired (consumed); q still armed. Move p, or unit on q.
                        auto new1 = find_unbroken(nogood, q, no_watch);
                        if (! new1)
                            inference.infer(logger, ! nogood[q], JustifyUsingRUP{}, generic_reason(vars));
                        else {
                            ctx.watch(nogood[*new1], key);
                            ctx.set_watch_state(key, pack(*new1, q));
                        }
                    }
                    else {
                        // Watch at q fired (consumed); p still armed. Move q, or unit on p.
                        auto new2 = find_unbroken(nogood, p, no_watch);
                        if (! new2)
                            inference.infer(logger, ! nogood[p], JustifyUsingRUP{}, generic_reason(vars));
                        else {
                            ctx.watch(nogood[*new2], key);
                            ctx.set_watch_state(key, pack(p, *new2));
                        }
                    }
                }
                return PropagatorState::Enable;
            },
            Triggers{});
    }
}

auto Nogoods::install_propagators(Propagators & propagators) -> void
{
    // The nogood data is shared with the store, so additions are visible here.
    if (_refined)
        install_refined_nogoods(propagators, constraint_id(), _store->_nogoods, _store->_vars);
    else
        install_scan_nogoods(propagators, constraint_id(), _store->_nogoods, _store->_vars, _trigger_vars);
}

auto Nogoods::constraint_type() const -> string
{
    return "nogoods";
}

auto Nogoods::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    // Each nogood is a list of (variable op value) condition terms. This is not
    // part of the CakePB workflow (which has no `nogoods` rule), but s_expr is
    // still invoked whenever a .scp is written, so it must produce valid output.
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> nogood_terms;
    for (const auto & nogood : *_store->_nogoods) {
        vector<SExpr> conditions;
        for (const auto & lit : nogood)
            conditions.push_back(SExpr::list(
                {SExpr::atom(tracker.s_expr_name_of(lit.var)), SExpr::atom(tracker.s_expr_name_of(lit.op)), SExpr::atom(lit.value.to_string())}));
        nogood_terms.push_back(SExpr::list(std::move(conditions)));
    }
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(nogood_terms))});
}
