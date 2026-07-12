#include <gcs/exception.hh>
#include <gcs/innards/conflict_observer.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/hints.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <optional>
#include <span>
#include <string>
#include <unordered_map>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::make_unique;
using std::move;
using std::optional;
using std::pair;
using std::string;
using std::swap;
using std::to_underlying;
using std::vector;
using std::visit;
using std::ranges::adjacent_find;
using std::ranges::contains;
using std::ranges::sort;

namespace
{
    struct TriggerIDs
    {
        vector<pair<int, int>> ids_and_masks;
    };

    // The GCS_CHECK_IDEMPOTENT_CLAIMS re-run: the claim says an immediate
    // re-run, against the domains exactly as the claiming run left them,
    // infers nothing and does not contradict. Check exactly that; a passing
    // re-run emits nothing, so proofs are unaffected. The re-run's own
    // PropagatorState is meaningless (the claim covered the first run) and is
    // discarded. Out of line and noinline so its exception-handling region
    // stays out of the propagation loop, whose per-run cost is measurable in
    // whole-program benchmarks.
    template <typename Tracker_>
    [[gnu::noinline]] auto recheck_idempotence_claim_or_throw(PropagationFunction & f, const State & state, Tracker_ & tracker,
        ProofLogger * const logger, const RefinedWatchContext & watches, const ConstraintID & id) -> void
    {
        const auto inferences_before_recheck = tracker.count_inferences();
        tracker.begin_propagator_run();
        try {
            (void)f(state, tracker, logger, watches);
        }
        catch (const TrackedPropagationFailed &) {
        }
        if (tracker.contradicted() || tracker.count_inferences() != inferences_before_recheck)
            throw UnexpectedException{"propagator for constraint " + as_string(id) + " claimed idempotence, but re-running it did more"};
    }

    // A refined per-literal watch armed on a variable: when `literal` becomes
    // entailed, `payload` is delivered to propagator `owner`. `id` is a stable
    // identity used to find and undo the watch on backtrack. `trigger_mask` is the
    // set of Inference granularities that could make `literal` newly entailed (see
    // refined_watch_trigger_mask); a change outside it cannot fire this watch, so
    // the firing loop skips the test_literal for it.
    struct RefinedWatch
    {
        Literal literal;
        std::uint32_t payload;
        int owner;
        std::uint64_t id;
        unsigned trigger_mask;
    };

    enum class WatchEditOp
    {
        Added,
        Removed
    };

    // One entry on the refined-watch backtrack trail: an Added/Removed edit to the
    // watches armed on var_index, replayed in reverse to restore on backtrack.
    struct RefinedWatchEdit
    {
        WatchEditOp op;
        std::size_t var_index;
        RefinedWatch watch;
    };

    // The underlying simple-variable index of a variable id, or nullopt for a
    // constant (no variable change can fire on it).
    auto underlying_var_index(const IntegerVariableID & var) -> std::optional<std::size_t>
    {
        return overloaded{[](const SimpleIntegerVariableID & v) -> std::optional<std::size_t> { return v.index; },
            [](const ViewOfIntegerVariableID & v) -> std::optional<std::size_t> { return v.actual_variable.index; },
            [](const ConstantIntegerVariableID &) -> std::optional<std::size_t> { return std::nullopt; }}
            .visit(var);
    }

    // The underlying simple-variable index a literal's truth depends on, or nullopt
    // for a constant/true/false literal that no variable change can fire.
    auto underlying_var_index(const Literal & literal) -> std::optional<std::size_t>
    {
        return overloaded{[](const IntegerVariableCondition & cond) -> std::optional<std::size_t> { return underlying_var_index(cond.var); },
            [](const TrueLiteral &) -> std::optional<std::size_t> { return std::nullopt; },
            [](const FalseLiteral &) -> std::optional<std::size_t> { return std::nullopt; }}
            .visit(literal);
    }

    // Which Inference granularities can make `literal` newly entailed, as a bitmask
    // over Inference -- mirroring the coarse iv_triggers masks. `x == v` can only
    // become true when x is instantiated; `x >= k` / `x < k` only when a bound
    // moves (an interior removal never changes a bound); `x != v` on any value
    // removal. So the firing loop can skip the (expensive) test_literal for a watch
    // whose literal cannot have flipped under the current inference. The mask is
    // derived from the literal alone -- the engine knows each operator's entailment
    // semantics -- so every client benefits without passing anything extra.
    auto refined_watch_trigger_mask(const Literal & literal) -> unsigned
    {
        using enum VariableConditionOperator;
        auto bit = [](Inference i) { return 1u << to_underlying(i); };
        const auto on_instantiated = bit(Inference::Instantiated);
        const auto on_bounds = bit(Inference::BoundsChanged) | on_instantiated;
        const auto on_change = bit(Inference::InteriorValuesChanged) | on_bounds;
        return overloaded{[&](const IntegerVariableCondition & cond) -> unsigned {
                              switch (cond.op) {
                              case Equal: return on_instantiated;
                              case NotEqual: return on_change;
                              case GreaterEqual:
                              case Less: return on_bounds;
                              }
                              return on_change; // unreachable; conservative default
                          },
            [&](const TrueLiteral &) -> unsigned { return on_change; }, [&](const FalseLiteral &) -> unsigned { return on_change; }}
            .visit(literal);
    }
}

struct Propagators::Imp : RefinedWatchSink
{
    vector<PropagationFunction> propagation_functions;
    std::array<vector<InitialisationFunction>, number_of_initialiser_priorities> initialisation_functions_by_priority;

    // Every propagation function's index appears exactly once in queue, and lookup[id] always tells
    // us where that position is. The ready-to-propagate items are [enqueued_begin, enqueued_end);
    // we run them oldest-first (FIFO -- empirically far better than a stack, see Schulte & Stuckey,
    // "Efficient Constraint Propagation Engines"). The items between enqueued_end and idle_end - 1 do
    // not need to be propagated. Anything from idle_end onwards is disabled until backtrack. Items in
    // [0, enqueued_begin) have already been propagated this round and become idle again at the next
    // requeue.
    vector<int> queue, lookup;
    int enqueued_begin = 0, enqueued_end = 0, idle_end = 0;
    // Reused scratch for the disable-until-backtrack propagators of the current round
    // (see the run loop); a member so it isn't reallocated on every propagate() call.
    vector<int> to_disable;

    // One entry per run this round that returned EnableButIdempotent (and whose
    // claim is not ignored): runs are serial and the store applies inferences
    // immediately, so a run whose end left the tracker holding
    // end_inference_index inferences had seen every one of them -- its own
    // included -- and the round-boundary replay uses these to skip re-waking a
    // claiming propagator from any inference it had already seen. Ordered by
    // end_inference_index (non-decreasing) by construction. Cleared at every
    // round boundary (and at propagate() entry, since a contradiction or abort
    // ends a round without replaying it).
    struct IdempotentRunClaim
    {
        std::size_t end_inference_index;
        int propagator_id;
    };
    vector<IdempotentRunClaim> idempotent_run_claims;

    // Indexed by propagator id: 1 if install() found two trigger positions
    // aliasing the same underlying variable, in which case any
    // EnableButIdempotent this propagator returns is treated as Enable.
    vector<uint8_t> idempotence_claims_ignored;

    // Scratch, indexed by propagator id: set transiently during the boundary
    // replay for claimants that must not be woken by the inference currently
    // being replayed (it predates their run's end). All zeroes outside that
    // block.
    vector<uint8_t> claim_protected;

    unsigned long long total_propagations = 0, effectful_propagations = 0, contradicting_propagations = 0;
    vector<TriggerIDs> iv_triggers;
    vector<long> degrees;

    // The constraint each propagator belongs to. propagator_constraint_index is
    // indexed by propagator id and gives a dense constraint index; constraint_ids
    // is the inverse (dense index -> ConstraintID); constraint_index_of_id assigns
    // a fresh dense index on first sight of each ConstraintID.
    vector<int> propagator_constraint_index;
    vector<ConstraintID> constraint_ids;
    std::unordered_map<ConstraintID, int> constraint_index_of_id;

    // The scope of each propagator (indexed by propagator id): its trigger
    // variables with views resolved to the underlying simple variable and
    // duplicates removed. var_constraint_indices is the transpose aggregated by
    // constraint: indexed by variable index, the deduplicated dense constraint
    // indices that variable participates in. constraint_scope is the union of a
    // constraint's propagators' scopes (indexed by dense constraint index), used
    // for the |fut|>1 weighted-degree filter. All built alongside the triggers
    // in install().
    vector<vector<SimpleIntegerVariableID>> propagator_scope;
    vector<vector<int>> var_constraint_indices;
    vector<vector<SimpleIntegerVariableID>> constraint_scope;

    // Borrowed conflict observers, each notified when a propagator wipes out a
    // domain (see propagate). Attached at search start via add_conflict_observer;
    // the caller owns them. There can be several: a seq_search may chain several
    // stateful branchers, each carrying its own weighting, and every one needs
    // to see every conflict. Empty when there are no observers.
    vector<ConflictObserver *> conflict_observers;

    // Refined per-literal watches, parallel to (and leaving untouched) iv_triggers.
    // refined_watches_by_var[v] are the watches currently armed on variable v; on a
    // change to v each is tested and, if its literal is now entailed, its payload is
    // appended to inbox_by_propagator[owner], the owner is woken, and the watch is
    // consumed. Edits made while propagating go on refined_watch_edit_trail and are
    // undone on backtrack (one truncate callback per propagate(), replayed in
    // reverse); install-time base watches are not trailed. inbox_by_propagator is
    // transient within a propagate(): cleared after each propagator runs, with
    // pending_inbox_owners cleaning up any left non-empty by a contradiction.
    // next_refined_watch_id hands out a stable identity per watch for trail undo.
    vector<vector<RefinedWatch>> refined_watches_by_var;
    vector<vector<std::uint32_t>> inbox_by_propagator;
    vector<int> pending_inbox_owners;
    vector<RefinedWatchEdit> refined_watch_edit_trail;
    std::uint64_t next_refined_watch_id = 0;

    // Per-propagator backtrackable scratch (watch_state): watch_state_by_propagator[
    // owner][key] is a uint64 the propagator chooses the meaning of (e.g. the two
    // watched positions of a clause, packed). Writes are recorded on
    // watch_state_trail and undone by the same per-propagate() backtrack callback as
    // the watch edits, so the propagator's bookkeeping is restored in lockstep with
    // its watches.
    struct WatchStateEdit
    {
        int owner;
        std::uint32_t key;
        std::uint64_t old_value;
    };
    vector<vector<std::uint64_t>> watch_state_by_propagator;
    vector<WatchStateEdit> watch_state_trail;

    [[nodiscard]] auto watch_state_get(int owner, std::uint32_t key) const -> std::uint64_t override
    {
        if (owner < 0 || static_cast<std::size_t>(owner) >= watch_state_by_propagator.size())
            return 0;
        const auto & v = watch_state_by_propagator[owner];
        return key < v.size() ? v[key] : 0;
    }

    auto watch_state_set(int owner, std::uint32_t key, std::uint64_t value) -> void override
    {
        if (watch_state_by_propagator.size() <= static_cast<std::size_t>(owner))
            watch_state_by_propagator.resize(owner + 1);
        auto & v = watch_state_by_propagator[owner];
        if (v.size() <= key)
            v.resize(key + 1, 0);
        watch_state_trail.push_back({owner, key, v[key]});
        v[key] = value;
    }

    auto register_refined_watch(int owner, const Literal & literal, std::uint32_t payload, bool trailed) -> void
    {
        auto var_index = underlying_var_index(literal);
        if (! var_index)
            return;
        if (refined_watches_by_var.size() <= *var_index)
            refined_watches_by_var.resize(*var_index + 1);
        RefinedWatch w{literal, payload, owner, next_refined_watch_id++, refined_watch_trigger_mask(literal)};
        refined_watches_by_var[*var_index].push_back(w);
        if (trailed)
            refined_watch_edit_trail.push_back({WatchEditOp::Added, *var_index, w});
    }

    auto add_refined_watch(int owner_propagator, const Literal & literal, std::uint32_t payload) -> void override
    {
        register_refined_watch(owner_propagator, literal, payload, true);
    }

    [[nodiscard]] auto is_watching(int owner_propagator, const IntegerVariableID & var) const -> bool override
    {
        auto var_index = underlying_var_index(var);
        if (! var_index || refined_watches_by_var.size() <= *var_index)
            return false;
        for (const auto & w : refined_watches_by_var[*var_index])
            if (w.owner == owner_propagator)
                return true;
        return false;
    }
};

Propagators::Propagators() : _imp(make_unique<Imp>())
{
}

Propagators::~Propagators() = default;

Propagators::Propagators(Propagators &&) = default;

auto Propagators::operator=(Propagators &&) -> Propagators & = default;

auto Propagators::define_bound(const State & state, ProofModel * const optional_model, IntegerVariableID var, Bound which, Integer val) -> void
{
    switch (which) {
        using enum Bound;
    case Lower:
        if (state.lower_bound(var) >= val)
            return;
        if (optional_model)
            optional_model->add_constraint(WPBSum{} + 1_i * var >= val);
        install_initialiser([var, val](const State &, auto & inference, ProofLogger * const logger) {
            inference.infer(logger, var >= val, JustifyUsingRUP{}, NoReason{}, AssertionAnnotation{.hint_name = hints::InitialBound::hint_name});
        });
        return;
    case Upper:
        if (state.upper_bound(var) <= val)
            return;
        if (optional_model)
            optional_model->add_constraint(WPBSum{} + 1_i * var <= val);
        install_initialiser([var, val](const State &, auto & inference, ProofLogger * const logger) {
            inference.infer(logger, var <= val, JustifyUsingRUP{}, NoReason{}, AssertionAnnotation{.hint_name = hints::InitialBound::hint_name});
        });
        return;
    }
}

auto Propagators::install(const ConstraintID & constraint_id, PropagationFunction && f, const Triggers & triggers) -> void
{
    int id = _imp->propagation_functions.size();
    _imp->propagation_functions.emplace_back(move(f));

    auto [it, inserted] = _imp->constraint_index_of_id.try_emplace(constraint_id, static_cast<int>(_imp->constraint_ids.size()));
    if (inserted)
        _imp->constraint_ids.push_back(constraint_id);
    int constraint_index = it->second;
    _imp->propagator_constraint_index.push_back(constraint_index);

    // Record this propagator's scope (its trigger variables, views resolved and
    // deduplicated) and add it to each variable's constraint adjacency.
    auto & scope = _imp->propagator_scope.emplace_back();
    scope.reserve(triggers.on_change.size() + triggers.on_bounds.size() + triggers.on_instantiated.size());
    auto add_to_scope = [&](IntegerVariableID var) {
        overloaded{[&](const SimpleIntegerVariableID & v) {
                       if (! contains(scope, v))
                           scope.push_back(v);
                   },
            [&](const ViewOfIntegerVariableID & v) {
                if (! contains(scope, v.actual_variable))
                    scope.push_back(v.actual_variable);
            },
            [&](const ConstantIntegerVariableID &) {}}
            .visit(var);
    };
    for (const auto & v : triggers.on_change)
        add_to_scope(v);
    for (const auto & v : triggers.on_bounds)
        add_to_scope(v);
    for (const auto & v : triggers.on_instantiated)
        add_to_scope(v);
    for (const auto & refined : triggers.refined)
        if (auto cond = std::get_if<IntegerVariableCondition>(&refined.first))
            add_to_scope(cond->var);

    for (const auto & v : scope) {
        if (_imp->var_constraint_indices.size() <= v.index)
            _imp->var_constraint_indices.resize(v.index + 1);
        auto & indices = _imp->var_constraint_indices[v.index];
        if (! contains(indices, constraint_index))
            indices.push_back(constraint_index);
    }

    // The union of this constraint's propagators' scopes, aggregated by dense
    // constraint index (scope_of_constraint): the |future| > 1 filter of the
    // weighted-degree heuristic walks it.
    if (_imp->constraint_scope.size() <= static_cast<std::size_t>(constraint_index))
        _imp->constraint_scope.resize(constraint_index + 1);
    auto & cscope = _imp->constraint_scope[constraint_index];
    for (const auto & v : scope)
        if (! contains(cscope, v))
            cscope.push_back(v);

    // Most propagation algorithms are only idempotent when no two scope
    // positions alias the same underlying variable, and only the posted scope
    // (visible here, as the triggers) tells us whether they do: views hide
    // repeats from the author (x and -x + 3 alias), though a single +-x + c
    // view on its own is harmless, being a bijection on Z. (If a view kind
    // that is not a bijection is ever added -- a multiplier, say -- any
    // occurrence of it must flag the scope as risky, not just a repeat.) So
    // canonicalise every trigger variable and, on a repeat, ignore any
    // EnableButIdempotent claims this propagator makes: a false positive
    // merely restores the always-requeue behaviour.
    vector<unsigned long long> underlying_trigger_vars;
    auto add_underlying = [&](const IntegerVariableID & v) {
        overloaded{
            [&](const SimpleIntegerVariableID & sv) { underlying_trigger_vars.push_back(sv.index); },                 //
            [&](const ViewOfIntegerVariableID & vv) { underlying_trigger_vars.push_back(vv.actual_variable.index); }, //
            [&](const ConstantIntegerVariableID &) {}                                                                 //
        }
            .visit(v);
    };

    for (const auto & v : triggers.on_change) {
        trigger_on_change(v, id);
        increase_degree(v);
        add_underlying(v);
    }

    for (const auto & v : triggers.on_bounds) {
        trigger_on_bounds(v, id);
        increase_degree(v);
        add_underlying(v);
    }

    for (const auto & v : triggers.on_instantiated) {
        trigger_on_instantiated(v, id);
        increase_degree(v);
        add_underlying(v);
    }

    sort(underlying_trigger_vars);
    _imp->idempotence_claims_ignored.push_back(adjacent_find(underlying_trigger_vars) != underlying_trigger_vars.end() ? 1 : 0);

    for (const auto & [literal, payload] : triggers.refined) {
        if (auto cond = std::get_if<IntegerVariableCondition>(&literal))
            increase_degree(cond->var);
        _imp->register_refined_watch(id, literal, payload, false);
    }
}

auto Propagators::install_initialiser(InitialisationFunction && f, InitialiserPriority priority) -> void
{
    _imp->initialisation_functions_by_priority[to_underlying(priority)].emplace_back(move(f));
}

auto Propagators::initialise(State & state, ProofLogger * const logger) const -> bool
{
    for (auto & bucket : _imp->initialisation_functions_by_priority) {
        for (auto & f : bucket) {
            try {
                // As in propagate(): with no logger, run the lean tracker.
                if (logger) {
                    EagerProofLoggingInferenceTracker inf(state);
                    f(state, inf, logger);
                }
                else {
                    SimpleInferenceTracker inf(state);
                    f(state, inf, logger);
                }
            }
            catch (const TrackedPropagationFailed &) {
                return false;
            }
        }
    }

    return true;
}

auto Propagators::propagate(const Literals & guesses, State & state, ProofLogger * const logger, atomic<bool> * optional_abort_flag) const -> bool
{
    // Test-mode net for EnableButIdempotent (see propagators-fwd.hh): re-run
    // every honoured claim immediately and abort if it infers anything or
    // contradicts. Read once: the constraint test harness sets this before the
    // first solve in the process.
    static const bool check_idempotent_claims = nullptr != std::getenv("GCS_CHECK_IDEMPOTENT_CLAIMS");

    auto enqueue_if_idle = [&](const int p) {
        if (_imp->lookup[p] >= _imp->enqueued_end && _imp->lookup[p] < _imp->idle_end) {
            auto being_swapped_item = _imp->queue[_imp->enqueued_end];
            swap(_imp->queue[_imp->lookup[p]], _imp->queue[_imp->enqueued_end]);
            swap(_imp->lookup[p], _imp->lookup[being_swapped_item]);
            ++_imp->enqueued_end;
        }
    };

    auto requeue = [&](const SimpleIntegerVariableID & v, const Inference inf) {
        if (v.index < _imp->iv_triggers.size())
            for (auto & [p, mask] : _imp->iv_triggers[v.index].ids_and_masks)
                if (mask & (1 << to_underlying(inf)))
                    enqueue_if_idle(p);

        // Refined watches: fire any whose literal is now entailed, delivering the
        // payload to its owner and consuming the watch. A watch is only tested when
        // the current inference granularity is in its trigger_mask -- e.g. an `x==v`
        // watch is skipped on a mere bound move, since x==v can only become true when
        // x is instantiated. This gates the expensive test_literal; the firing of a
        // watch outside its mask would be a no-op anyway (the literal cannot have
        // changed status), so this is semantics-preserving.
        if (v.index < _imp->refined_watches_by_var.size()) {
            const auto inf_bit = 1u << to_underlying(inf);
            auto & watches = _imp->refined_watches_by_var[v.index];
            for (std::size_t i = 0; i < watches.size();) {
                if ((watches[i].trigger_mask & inf_bit) && state.test_literal(watches[i].literal) == LiteralIs::DefinitelyTrue) {
                    const auto fired = watches[i];
                    if (_imp->inbox_by_propagator[fired.owner].empty())
                        _imp->pending_inbox_owners.push_back(fired.owner);
                    _imp->inbox_by_propagator[fired.owner].push_back(fired.payload);
                    enqueue_if_idle(fired.owner);
                    _imp->refined_watch_edit_trail.push_back({WatchEditOp::Removed, v.index, fired});
                    watches[i] = watches.back();
                    watches.pop_back();
                }
                else
                    ++i;
            }
        }
    };

    // A run that claimed idempotence must not be re-woken by any inference it
    // had already seen (everything recorded up to its run's end, its own
    // inferences included): the round-boundary replay uses this variant, with
    // claim_protected flagging the claimants whose runs ended after the
    // inference being replayed, when (and only when) the round produced
    // claims -- the plain requeue above keeps the claim-free hot path free of
    // the extra load. Refined watches are consumed on their first fire in the
    // requeue above, so this coarse-only replay does not re-fire them.
    auto requeue_unless_already_seen = [&](const SimpleIntegerVariableID & v, const Inference inf) {
        if (v.index < _imp->iv_triggers.size())
            for (auto & [p, mask] : _imp->iv_triggers[v.index].ids_and_masks)
                if ((mask & (1 << to_underlying(inf))) && ! _imp->claim_protected[p])
                    enqueue_if_idle(p);
    };

    // A contradiction or an abort ends a round without replaying it, so a
    // previous propagate() call may have left stale claims behind. The
    // claim_protected flags need no such clearing: they are nonzero only
    // within the boundary-replay block itself, which always clears them
    // before running anything. Just make sure the scratch is big enough.
    _imp->idempotent_run_claims.clear();
    if (_imp->claim_protected.size() < _imp->propagation_functions.size())
        _imp->claim_protected.resize(_imp->propagation_functions.size(), 0);

    _imp->inbox_by_propagator.resize(_imp->propagation_functions.size());

    // Snapshot the refined-watch edit trail BEFORE any firing this call. The guess
    // first pass below can already fire and consume watches, so the snapshot must
    // precede it; otherwise those consumes fall below the snapshot and are never
    // undone, corrupting the watch state across sibling branches. On backtrack we
    // replay our own trail in reverse here (State runs an epoch's callbacks in
    // registration order, which would compose per-edit undos incorrectly), undoing
    // exactly the edits made during this propagate(). Install-time base watches are
    // registered before search and so sit below every snapshot and persist.
    auto refined_trail_start = _imp->refined_watch_edit_trail.size();
    auto watch_state_trail_start = _imp->watch_state_trail.size();
    state.on_backtrack([&, refined_trail_start, watch_state_trail_start]() {
        while (_imp->refined_watch_edit_trail.size() > refined_trail_start) {
            const auto & e = _imp->refined_watch_edit_trail.back();
            auto & watches = _imp->refined_watches_by_var[e.var_index];
            if (e.op == WatchEditOp::Added) {
                for (std::size_t i = 0; i < watches.size(); ++i)
                    if (watches[i].id == e.watch.id) {
                        watches[i] = watches.back();
                        watches.pop_back();
                        break;
                    }
            }
            else
                watches.push_back(e.watch);
            _imp->refined_watch_edit_trail.pop_back();
        }
        // Restore the per-propagator backtrackable scratch in lockstep, so any
        // bookkeeping a propagator kept in it (e.g. its watched positions) matches
        // the watches just restored above.
        while (_imp->watch_state_trail.size() > watch_state_trail_start) {
            const auto & e = _imp->watch_state_trail.back();
            _imp->watch_state_by_propagator[e.owner][e.key] = e.old_value;
            _imp->watch_state_trail.pop_back();
        }
    });

    if (guesses.empty()) {
        // On the first pass, walk propagators in registration order. The queue runs
        // oldest-first, so push them forwards.
        _imp->queue.resize(_imp->propagation_functions.size());
        _imp->lookup.resize(_imp->propagation_functions.size());
        for (unsigned i = 0; i != _imp->propagation_functions.size(); ++i) {
            _imp->queue[i] = i;
            _imp->lookup[i] = i;
        }

        _imp->enqueued_begin = 0;
        _imp->enqueued_end = _imp->propagation_functions.size();
        _imp->idle_end = _imp->propagation_functions.size();
    }
    else {
        // Seed the queue from every supplied guess. A propagator already enqueued by an
        // earlier guess is skipped by the bookkeeping inside requeue, so guesses sharing
        // a variable do not double-enqueue.
        _imp->enqueued_begin = 0;
        _imp->enqueued_end = 0;
        for (const auto & lit : guesses) {
            overloaded{
                [&](const TrueLiteral &) {},  //
                [&](const FalseLiteral &) {}, //
                [&](const IntegerVariableCondition & cond) {
                    overloaded{
                        [&](const SimpleIntegerVariableID & var) {
                            // trigger all propagators on this var, even if we might not actually
                            // have instantiated it. bit ugly but easier than tracking.
                            requeue(var, Inference::Instantiated);
                        },                                                                                                  //
                        [&](const ConstantIntegerVariableID &) {},                                                          //
                        [&](const ViewOfIntegerVariableID & var) { requeue(var.actual_variable, Inference::Instantiated); } //
                    }
                        .visit(cond.var);
                } //
            }
                .visit(lit);
        }
    }

    auto orig_idle_end = _imp->idle_end;
    state.on_backtrack([&, orig_idle_end = orig_idle_end]() { _imp->idle_end = orig_idle_end; });

    // The loop body is identical for either tracker (it only uses the shared base
    // interface plus the dual-overloaded propagation-function call), so run it on a
    // generic lambda. With no logger we use the lean SimpleInferenceTracker, whose
    // proofs-off path carries no reason snapshotting or proof-logging code.
    auto run = [&](auto & tracker) -> bool {
        bool contradiction = false;
        _imp->to_disable.clear();
        while (! contradiction) {
            if (_imp->enqueued_begin == _imp->enqueued_end) {
                // The ready queue has drained. Retire any propagators that asked to be
                // disabled this round -- deferred to here, where the just-propagated
                // prefix [0, enqueued_begin) and the idle tail form one contiguous
                // [0, idle_end) block, so each swap-to-disabled has a valid target even
                // when the idle region emptied mid-round. lookup[] is kept current by
                // the swaps, so processing order does not matter.
                for (auto disable_id : _imp->to_disable) {
                    --_imp->idle_end;
                    auto being_swapped_item = _imp->queue[_imp->idle_end];
                    swap(_imp->queue[_imp->lookup[disable_id]], _imp->queue[_imp->idle_end]);
                    swap(_imp->lookup[disable_id], _imp->lookup[being_swapped_item]);
                }
                _imp->to_disable.clear();

                // Fold the propagated prefix back into the idle region and wake the
                // propagators triggered by this round's inferences. each_inference() yields
                // oldest-first, so propagators are requeued in the order their triggers
                // occurred -- keeping the queue properly FIFO (the drain is already FIFO).
                // An inference must not re-wake a claiming propagator whose run ended
                // after it was recorded: that propagator had already seen it (the store
                // applies inferences immediately, and its claim says re-running against
                // what it saw infers nothing). Runs are serial, so the claims are
                // ordered by end index, and a single cursor un-protects each claimant
                // as the replay passes its run's end. (This can delay work by a round
                // relative to the unclaimed engine: a re-woken run there sees, for
                // free, changes made after the wake it was requeued by, where the
                // claiming engine waits for those changes to wake it at the next
                // boundary. Both reach the same per-node fixpoint -- propagators are
                // monotone, so the fixpoint is unique and the search tree identical --
                // but inference attribution, and hence proof lines, the total and
                // effectful propagation counts, can differ in either direction.)
                _imp->enqueued_begin = 0;
                _imp->enqueued_end = 0;
                if (_imp->idempotent_run_claims.empty()) {
                    for (const auto & [v, inf] : tracker.each_inference())
                        requeue(v, inf);
                }
                else {
                    for (const auto & c : _imp->idempotent_run_claims)
                        _imp->claim_protected[c.propagator_id] = 1;
                    auto claim = _imp->idempotent_run_claims.begin();
                    const auto claims_end = _imp->idempotent_run_claims.end();
                    std::size_t inference_index = 0;
                    for (const auto & [v, inf] : tracker.each_inference()) {
                        while (claim != claims_end && claim->end_inference_index <= inference_index) {
                            _imp->claim_protected[claim->propagator_id] = 0;
                            ++claim;
                        }
                        requeue_unless_already_seen(v, inf);
                        ++inference_index;
                    }
                    for (; claim != claims_end; ++claim)
                        _imp->claim_protected[claim->propagator_id] = 0;
                    _imp->idempotent_run_claims.clear();
                }
                tracker.reset();
            }

            if (_imp->enqueued_begin == _imp->enqueued_end)
                break;

            int propagator_id = _imp->queue[_imp->enqueued_begin++];
            try {
                ++_imp->total_propagations;
                tracker.begin_propagator_run();
                RefinedWatchContext watches{*_imp, propagator_id, _imp->inbox_by_propagator[propagator_id]};
                auto propagator_state = _imp->propagation_functions[propagator_id](state, tracker, logger, watches);
                // The fired set has now been delivered; clear it so that, if this
                // propagator is woken again later in this fixpoint, it sees only the
                // payloads that fired since.
                _imp->inbox_by_propagator[propagator_id].clear();
                if (tracker.contradicted()) {
                    // A propagator that opted into the non-throwing failure path
                    // (infer_*_or_stop) signals contradiction with this flag rather
                    // than by unwinding; throwing propagators are caught below.
                    contradiction = true;
                    ++_imp->contradicting_propagations;
                }
                else {
                    if (tracker.did_anything_since_last_call_by_propagation_queue())
                        ++_imp->effectful_propagations;
                    switch (propagator_state) {
                    case PropagatorState::Enable: break;
                    case PropagatorState::EnableButIdempotent:
                        // An ignored claim (aliased trigger scope, see install)
                        // just behaves like Enable. Every other claiming run is
                        // recorded, even one that inferred nothing: the record
                        // protects the claimant from being re-woken by anything
                        // it had already seen, and a no-op run saw everything
                        // recorded so far just the same. A run that ended before
                        // the round's first inference has nothing to be
                        // protected from, though, and leaving it out keeps the
                        // boundary replay on its claim-free fast path in rounds
                        // where the claimants all came up empty early.
                        if (! _imp->idempotence_claims_ignored[propagator_id]) {
                            if (check_idempotent_claims) [[unlikely]] {
                                RefinedWatchContext recheck_watches{*_imp, propagator_id, {}};
                                recheck_idempotence_claim_or_throw(_imp->propagation_functions[propagator_id], state, tracker, logger,
                                    recheck_watches, _imp->constraint_ids[_imp->propagator_constraint_index[propagator_id]]);
                            }
                            if (const auto seen = tracker.count_inferences(); 0 != seen)
                                _imp->idempotent_run_claims.emplace_back(seen, propagator_id);
                        }
                        break;
                    case PropagatorState::DisableUntilBacktrack: _imp->to_disable.push_back(propagator_id); break;
                    }
                }
            }
            catch (const TrackedPropagationFailed &) {
                contradiction = true;
                ++_imp->contradicting_propagations;
                // Exactly one propagator contradiction ends each propagate(), so this
                // fires at most once per call. Non-propagator contradiction paths
                // (initialisers, the objective bound) never reach here, so they are
                // not attributed to any constraint.
                for (auto & observer : _imp->conflict_observers)
                    observer->note_conflict(_imp->propagator_constraint_index[propagator_id], _imp->propagator_scope[propagator_id],
                        tracker.last_contradiction_reason(), state);
            }

            if (contradiction || (optional_abort_flag && optional_abort_flag->load()))
                break;
        }

        // Drop any fired payloads left undelivered (e.g. a propagator was woken but a
        // contradiction ended the loop before it ran); they must not leak into the next
        // propagate(). In the normal case each propagator already cleared its own.
        for (auto owner : _imp->pending_inbox_owners)
            _imp->inbox_by_propagator[owner].clear();
        _imp->pending_inbox_owners.clear();

        return ! contradiction;
    };

    if (logger) {
        EagerProofLoggingInferenceTracker tracker{state};
        return run(tracker);
    }
    else {
        SimpleInferenceTracker tracker{state};
        return run(tracker);
    }
}

auto Propagators::fill_in_constraint_stats(Stats & stats) const -> void
{
    stats.n_propagators += _imp->propagation_functions.size();
    stats.propagations += _imp->total_propagations;
    stats.effectful_propagations += _imp->effectful_propagations;
    stats.contradicting_propagations += _imp->contradicting_propagations;
    for (const auto & ignored : _imp->idempotence_claims_ignored)
        stats.idempotence_downgrades += ignored;
}

auto Propagators::trigger_on_change(IntegerVariableID var, int t) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->iv_triggers.size() <= v.index)
                _imp->iv_triggers.resize(v.index + 1);
            _imp->iv_triggers[v.index].ids_and_masks.emplace_back(t,
                (1 << to_underlying(Inference::InteriorValuesChanged)) | (1 << to_underlying(Inference::BoundsChanged)) |
                    (1 << to_underlying(Inference::Instantiated)));
        },                                                                                   //
        [&](const ViewOfIntegerVariableID & v) { trigger_on_change(v.actual_variable, t); }, //
        [&](const ConstantIntegerVariableID &) {}                                            //
    }
        .visit(var);
}

auto Propagators::trigger_on_bounds(IntegerVariableID var, int t) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->iv_triggers.size() <= v.index)
                _imp->iv_triggers.resize(v.index + 1);
            _imp->iv_triggers[v.index].ids_and_masks.emplace_back(
                t, (1 << to_underlying(Inference::BoundsChanged)) | (1 << to_underlying(Inference::Instantiated)));
        },                                                                                   //
        [&](const ViewOfIntegerVariableID & v) { trigger_on_bounds(v.actual_variable, t); }, //
        [&](const ConstantIntegerVariableID &) {}                                            //
    }
        .visit(var);
}

auto Propagators::trigger_on_instantiated(IntegerVariableID var, int t) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->iv_triggers.size() <= v.index)
                _imp->iv_triggers.resize(v.index + 1);
            _imp->iv_triggers[v.index].ids_and_masks.emplace_back(t, (1 << to_underlying(Inference::Instantiated)));
        },                                                                                         //
        [&](const ViewOfIntegerVariableID & v) { trigger_on_instantiated(v.actual_variable, t); }, //
        [&](const ConstantIntegerVariableID &) {}                                                  //
    }
        .visit(var);
}

auto Propagators::increase_degree(IntegerVariableID var) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->degrees.size() < v.index + 1)
                _imp->degrees.resize(v.index + 1);
            ++_imp->degrees[v.index];
        },                                                                              //
        [&](const ViewOfIntegerVariableID & v) { increase_degree(v.actual_variable); }, //
        [&](const ConstantIntegerVariableID &) {}                                       //
    }
        .visit(var);
}

auto Propagators::degree_of(IntegerVariableID var) const -> long
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> long {
            if (v.index >= _imp->degrees.size())
                return 0;
            else
                return _imp->degrees[v.index];
        },                                                                                       //
        [&](const ViewOfIntegerVariableID & v) -> long { return degree_of(v.actual_variable); }, //
        [&](const ConstantIntegerVariableID &) -> long { return 0; }                             //
    }
        .visit(var);
}

auto Propagators::number_of_constraints() const -> std::size_t
{
    return _imp->constraint_ids.size();
}

auto Propagators::constraint_index_of_propagator(int propagator_id) const -> int
{
    return _imp->propagator_constraint_index[propagator_id];
}

auto Propagators::constraint_id_for_index(int constraint_index) const -> const ConstraintID &
{
    return _imp->constraint_ids[constraint_index];
}

auto Propagators::scope_of_propagator(int propagator_id) const -> const vector<SimpleIntegerVariableID> &
{
    return _imp->propagator_scope[propagator_id];
}

auto Propagators::constraint_indices_of_variable(SimpleIntegerVariableID var) const -> const vector<int> &
{
    if (var.index >= _imp->var_constraint_indices.size()) {
        static const vector<int> none;
        return none;
    }
    return _imp->var_constraint_indices[var.index];
}

auto Propagators::scope_of_constraint(int constraint_index) const -> const vector<SimpleIntegerVariableID> &
{
    return _imp->constraint_scope[constraint_index];
}

auto Propagators::add_conflict_observer(ConflictObserver * observer) -> void
{
    _imp->conflict_observers.push_back(observer);
}

auto Propagators::conflict_observers() const -> const vector<ConflictObserver *> &
{
    return _imp->conflict_observers;
}
