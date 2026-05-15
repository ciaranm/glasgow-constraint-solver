#include <gcs/exception.hh>
#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <array>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::move;
using std::optional;
using std::pair;
using std::string;
using std::swap;
using std::to_underlying;
using std::vector;
using std::visit;

namespace
{
    struct TriggerIDs
    {
        vector<pair<int, int>> ids_and_masks;
    };
}

struct Propagators::Imp
{
    vector<PropagationFunction> propagation_functions;
    std::array<vector<InitialisationFunction>, number_of_initialiser_priorities> initialisation_functions_by_priority;

    // Every propagation function's index appears exactly once in queue, and lookup[id] always tells
    // us where that position is. The items from index 0 to enqueued_end - 1 are ready to be
    // propagated, and the items between enqueued_end and idle_end - 1 do not need to be propagated.
    // Anything from idle_end onwards is disabled until backtrack.
    vector<int> queue, lookup;
    int enqueued_end = 0, idle_end = 0;

    unsigned long long total_propagations = 0, effectful_propagations = 0, contradicting_propagations = 0;
    vector<TriggerIDs> iv_triggers;
    vector<long> degrees;
};

Propagators::Propagators() :
    _imp(new Imp())
{
}

Propagators::~Propagators() = default;

Propagators::Propagators(Propagators &&) = default;

auto Propagators::operator=(Propagators &&) -> Propagators & = default;

auto Propagators::define_bound(const State & state, ProofModel * const optional_model,
    IntegerVariableID var, Bound which, Integer val,
    const StringLiteral & constraint_name, const StringLiteral & sub_rule) -> void
{
    switch (which) {
        using enum Bound;
    case Lower:
        if (state.lower_bound(var) >= val)
            return;
        if (optional_model)
            optional_model->add_constraint(constraint_name, sub_rule, WPBSum{} + 1_i * var >= val);
        install_initialiser([var, val](const State &, auto & inference, ProofLogger * const logger) {
            inference.infer(logger, var >= val, JustifyUsingRUP{}, ReasonFunction{});
        });
        return;
    case Upper:
        if (state.upper_bound(var) <= val)
            return;
        if (optional_model)
            optional_model->add_constraint(constraint_name, sub_rule, WPBSum{} + 1_i * var <= val);
        install_initialiser([var, val](const State &, auto & inference, ProofLogger * const logger) {
            inference.infer(logger, var <= val, JustifyUsingRUP{}, ReasonFunction{});
        });
        return;
    }
}

auto Propagators::install(PropagationFunction && f, const Triggers & triggers) -> void
{
    int id = _imp->propagation_functions.size();
    _imp->propagation_functions.emplace_back(move(f));

    for (const auto & v : triggers.on_change) {
        trigger_on_change(v, id);
        increase_degree(v);
    }

    for (const auto & v : triggers.on_bounds) {
        trigger_on_bounds(v, id);
        increase_degree(v);
    }

    for (const auto & v : triggers.on_instantiated) {
        trigger_on_instantiated(v, id);
        increase_degree(v);
    }
}

auto Propagators::install_initialiser(InitialisationFunction && f, InitialiserPriority priority) -> void
{
    _imp->initialisation_functions_by_priority[to_underlying(priority)].emplace_back(move(f));
}

auto Propagators::install_initial_contradiction(const string &, Justification why, ReasonFunction reason, InitialiserPriority priority) -> void
{
    install_initialiser(
        [why = move(why), reason = move(reason)](const State &, auto & inference, ProofLogger * const logger) -> void {
            inference.contradiction(logger, why, reason);
        },
        priority);
}

auto Propagators::initialise(State & state, ProofLogger * const logger) const -> bool
{
    for (auto & bucket : _imp->initialisation_functions_by_priority) {
        for (auto & f : bucket) {
            EagerProofLoggingInferenceTracker inf(state);
            try {
                f(state, inf, logger);
            }
            catch (const TrackedPropagationFailed &) {
                return false;
            }
        }
    }

    return true;
}

auto Propagators::propagate(const optional<Literal> & lit, State & state, ProofLogger * const logger, atomic<bool> * optional_abort_flag) const -> bool
{
    auto requeue = [&](const SimpleIntegerVariableID & v, const Inference inf) {
        if (v.index < _imp->iv_triggers.size()) {
            auto & triggers = _imp->iv_triggers[v.index];

            for (auto & [p, mask] : triggers.ids_and_masks)
                if (mask & (1 << to_underlying(inf))) {
                    if (_imp->lookup[p] >= _imp->enqueued_end && _imp->lookup[p] < _imp->idle_end) {
                        auto being_swapped_item = _imp->queue[_imp->enqueued_end];
                        swap(_imp->queue[_imp->lookup[p]], _imp->queue[_imp->enqueued_end]);
                        swap(_imp->lookup[p], _imp->lookup[being_swapped_item]);
                        ++_imp->enqueued_end;
                    }
                }
        }
    };

    if (! lit) {
        // On the first pass, walk propagators in registration order. Our queue runs
        // backwards, so push them in reverse.
        _imp->queue.resize(_imp->propagation_functions.size());
        _imp->lookup.resize(_imp->propagation_functions.size());
        unsigned p = 0;
        for (int i = _imp->propagation_functions.size() - 1; i >= 0; --i) {
            _imp->queue[p] = i;
            _imp->lookup[i] = p;
            ++p;
        }

        _imp->enqueued_end = _imp->propagation_functions.size();
        _imp->idle_end = _imp->propagation_functions.size();
    }
    else {
        _imp->enqueued_end = 0;
        overloaded{
            [&](const TrueLiteral &) {},
            [&](const FalseLiteral &) {},
            [&](const IntegerVariableCondition & cond) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        // trigger all propagators on this var, even if we might not actually
                        // have instantiated it. bit ugly but easier than tracking.
                        requeue(var, Inference::Instantiated);
                    },
                    [&](const ConstantIntegerVariableID &) {
                    },
                    [&](const ViewOfIntegerVariableID & var) {
                        requeue(var.actual_variable, Inference::Instantiated);
                    }}
                    .visit(cond.var);
            }}
            .visit(*lit);
    }

    auto orig_idle_end = _imp->idle_end;
    state.on_backtrack([&, orig_idle_end = orig_idle_end]() {
        _imp->idle_end = orig_idle_end;
    });

    EagerProofLoggingInferenceTracker tracker{state};

    bool contradiction = false;
    while (! contradiction) {
        if (0 == _imp->enqueued_end) {
            for (const auto & [v, inf] : tracker.each_inference())
                requeue(v, inf);
            tracker.reset();
        }

        if (0 == _imp->enqueued_end)
            break;

        int propagator_id = _imp->queue[--_imp->enqueued_end];
        try {
            ++_imp->total_propagations;
            auto propagator_state = _imp->propagation_functions[propagator_id](state, tracker, logger);
            if (tracker.did_anything_since_last_call_by_propagation_queue())
                ++_imp->effectful_propagations;
            switch (propagator_state) {
            case PropagatorState::Enable:
                break;
            case PropagatorState::DisableUntilBacktrack:
                --_imp->idle_end;
                auto being_swapped_item = _imp->queue[_imp->idle_end];
                swap(_imp->queue[_imp->enqueued_end], _imp->queue[_imp->idle_end]);
                swap(_imp->lookup[propagator_id], _imp->lookup[being_swapped_item]);
                break;
            }
        }
        catch (const TrackedPropagationFailed &) {
            contradiction = true;
            ++_imp->contradicting_propagations;
        }

        if (contradiction || (optional_abort_flag && optional_abort_flag->load()))
            break;
    }

    return ! contradiction;
}

auto Propagators::fill_in_constraint_stats(Stats & stats) const -> void
{
    stats.n_propagators += _imp->propagation_functions.size();
    stats.propagations += _imp->total_propagations;
    stats.effectful_propagations += _imp->effectful_propagations;
    stats.contradicting_propagations += _imp->contradicting_propagations;
}

auto Propagators::trigger_on_change(IntegerVariableID var, int t) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->iv_triggers.size() <= v.index)
                _imp->iv_triggers.resize(v.index + 1);
            _imp->iv_triggers[v.index].ids_and_masks.emplace_back(t,
                (1 << to_underlying(Inference::InteriorValuesChanged)) |
                    (1 << to_underlying(Inference::BoundsChanged)) |
                    (1 << to_underlying(Inference::Instantiated)));
        },
        [&](const ViewOfIntegerVariableID & v) {
            trigger_on_change(v.actual_variable, t);
        },
        [&](const ConstantIntegerVariableID &) {
        }}
        .visit(var);
}

auto Propagators::trigger_on_bounds(IntegerVariableID var, int t) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->iv_triggers.size() <= v.index)
                _imp->iv_triggers.resize(v.index + 1);
            _imp->iv_triggers[v.index].ids_and_masks.emplace_back(t,
                (1 << to_underlying(Inference::BoundsChanged)) |
                    (1 << to_underlying(Inference::Instantiated)));
        },
        [&](const ViewOfIntegerVariableID & v) {
            trigger_on_bounds(v.actual_variable, t);
        },
        [&](const ConstantIntegerVariableID &) {
        }}
        .visit(var);
}

auto Propagators::trigger_on_instantiated(IntegerVariableID var, int t) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->iv_triggers.size() <= v.index)
                _imp->iv_triggers.resize(v.index + 1);
            _imp->iv_triggers[v.index].ids_and_masks.emplace_back(t,
                (1 << to_underlying(Inference::Instantiated)));
        },
        [&](const ViewOfIntegerVariableID & v) {
            trigger_on_instantiated(v.actual_variable, t);
        },
        [&](const ConstantIntegerVariableID &) {
        }}
        .visit(var);
}

auto Propagators::increase_degree(IntegerVariableID var) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->degrees.size() < v.index + 1)
                _imp->degrees.resize(v.index + 1);
            ++_imp->degrees[v.index];
        },
        [&](const ViewOfIntegerVariableID & v) {
            increase_degree(v.actual_variable);
        },
        [&](const ConstantIntegerVariableID &) {
        }}
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
        },
        [&](const ViewOfIntegerVariableID & v) -> long {
            return degree_of(v.actual_variable);
        },
        [&](const ConstantIntegerVariableID &) -> long {
            return 0;
        }}
        .visit(var);
}
