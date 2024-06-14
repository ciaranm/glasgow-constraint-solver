#include <gcs/exception.hh>
#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <bit>
#include <chrono>
#include <list>
#include <set>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::bit_ceil;
using std::function;
using std::in_place_type;
using std::list;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::swap;
using std::variant;
using std::vector;
using std::visit;

namespace
{
    struct TriggerIDs
    {
        vector<pair<int, int> > ids_and_masks;
    };
}

struct Propagators::Imp
{
    vector<variant<PropagationFunction, EagerPropagationFunction>> propagation_functions;
    vector<InitialisationFunction> initialisation_functions;

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

auto Propagators::model_contradiction(const State &, ProofModel * const optional_model, const string & explain_yourself) -> void
{
    if (optional_model)
        optional_model->add_constraint({});

    install_initialiser([explain_yourself = explain_yourself](const State &, ProofLogger * const, auto & inference) -> void {
        inference.infer_false(JustifyUsingRUP{}, Reason{[=]() { return Literals{}; }});
    });
}

auto Propagators::trim_lower_bound(const State & state, ProofModel * const optional_model, IntegerVariableID var, Integer val, const string & x) -> void
{
    if (state.lower_bound(var) < val) {
        if (state.upper_bound(var) >= val) {
            if (optional_model)
                optional_model->add_constraint({var >= val});
            install_initialiser([var, val](const State &, ProofLogger * const, auto & inference) {
                inference.infer(var >= val, JustifyUsingRUP{}, Reason{});
            });
        }
        else
            model_contradiction(state, optional_model, "Trimmed lower bound of " + debug_string(var) + " due to " + x + " is outside its domain");
    }
}

auto Propagators::trim_upper_bound(const State & state, ProofModel * const optional_model, IntegerVariableID var, Integer val, const string & x) -> void
{
    if (state.upper_bound(var) > val) {
        if (state.lower_bound(var) <= val) {
            if (optional_model)
                optional_model->add_constraint({var < val + 1_i});
            install_initialiser([var, val](const State &, ProofLogger * const, auto & inference) {
                inference.infer(var < val + 1_i, JustifyUsingRUP{}, Reason{});
            });
        }
        else
            model_contradiction(state, optional_model, "Trimmed upper bound of " + debug_string(var) + " due to " + x + " is outside its domain");
    }
}

auto Propagators::install(PropagationFunction && f, const Triggers & triggers, const string &) -> void
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

auto Propagators::install_eager_only(EagerPropagationFunction && f, const Triggers & triggers, const string &) -> void
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

auto Propagators::install_initialiser(InitialisationFunction && f) -> void
{
    _imp->initialisation_functions.emplace_back(move(f));
}

namespace
{
    auto is_immediately_infeasible(const IntegerVariableID & var, const Integer & val) -> bool
    {
        return is_literally_false(var == val);
    }

    auto is_immediately_infeasible(const IntegerVariableID &, const Wildcard &) -> bool
    {
        return false;
    }

    auto is_immediately_infeasible(const IntegerVariableID & var, const IntegerOrWildcard & val) -> bool
    {
        return visit([&](const auto & val) { return is_immediately_infeasible(var, val); }, val);
    }

    auto add_lit_unless_immediately_true(WeightedPseudoBooleanSum & lits, const IntegerVariableID & var, const Integer & val) -> void
    {
        if (! is_literally_true(var == val))
            lits += 1_i * (var == val);
    }

    auto add_lit_unless_immediately_true(WeightedPseudoBooleanSum &, const IntegerVariableID &, const Wildcard &) -> void
    {
    }

    auto add_lit_unless_immediately_true(WeightedPseudoBooleanSum & lits, const IntegerVariableID & var, const IntegerOrWildcard & val) -> void
    {
        return visit([&](const auto & val) { add_lit_unless_immediately_true(lits, var, val); }, val);
    }

    template <typename T_>
    auto depointinate(const std::shared_ptr<const T_> & t) -> const T_ &
    {
        return *t;
    }

    template <typename T_>
    auto depointinate(const T_ & t) -> const T_ &
    {
        return t;
    }
}

auto Propagators::define_and_install_table(State & state, ProofModel * const optional_model, const vector<IntegerVariableID> & vars,
    ExtensionalTuples permitted, const string & x) -> void
{
    visit([&](auto && permitted) {
        if (depointinate(permitted).empty()) {
            model_contradiction(state, optional_model, "Empty table constraint from " + x);
            return;
        }

        auto selector = state.allocate_integer_variable_with_state(0_i, Integer(depointinate(permitted).size() - 1));
        if (optional_model)
            optional_model->set_up_integer_variable(selector, 0_i, Integer(depointinate(permitted).size() - 1), "aux_table", nullopt);

        // pb encoding, if necessary
        if (optional_model) {
            for (const auto & [tuple_idx, tuple] : enumerate(depointinate(permitted))) {
                // selector == tuple_idx -> /\_i vars[i] == tuple[i]
                bool infeasible = false;
                WeightedPseudoBooleanSum lits;
                lits += Integer(tuple.size()) * (selector != Integer(tuple_idx));
                for (const auto & [var_idx, var] : enumerate(vars)) {
                    if (is_immediately_infeasible(var, tuple[var_idx]))
                        infeasible = true;
                    else
                        add_lit_unless_immediately_true(lits, var, tuple[var_idx]);
                }
                if (infeasible)
                    optional_model->add_constraint({selector != Integer(tuple_idx)});
                else
                    optional_model->add_constraint(lits >= Integer(lits.terms.size() - 1));
            }
        }

        Triggers triggers;
        for (auto & v : vars)
            triggers.on_change.push_back(v);
        triggers.on_change.push_back(selector);

        install([table = ExtensionalData{selector, move(vars), move(permitted)}](
                    const State & state, auto & inference) -> PropagatorState {
            return propagate_extensional(table, state, inference);
        },
            triggers, "extenstional");
    },
        move(permitted));
}

auto Propagators::initialise(State & state, ProofLogger * const logger, SomeKindOfInferenceTracker & inference) const -> bool
{
    for (auto & f : _imp->initialisation_functions) {
        if (! visit([&](auto && inference) -> bool {
                try {
                    f(state, logger, inference);
                    return true;
                }
                catch (const TrackedPropagationFailed &) {
                    return false;
                }
            },
                inference))
            return false;
    }

    return true;
}

auto Propagators::propagate(State & state, ProofLogger * const logger,
    SomeKindOfInferenceTracker & inference,
    const optional<pair<Literal, HowChanged>> & start_from_guess_rather_than_all_propagators,
    atomic<bool> * optional_abort_flag) const -> bool
{
    list<int> queue;
    set<int> on_queue, disabled;

    auto requeue_variable = [&](const SimpleIntegerVariableID & var, HowChanged how) {
        if (var.index < _imp->iv_triggers.size()) {
            auto & triggers = _imp->iv_triggers[var.index];

            for (auto & [p, mask] : triggers.ids_and_masks)
                if (mask & (1 << static_cast<int>(how))) {
                    if (! on_queue.contains(p) && ! disabled.contains(p)) {
                        on_queue.emplace(p);
                        queue.push_back(p);
                    }
                }
        }
    };

    auto requeue_literal = [&](const Literal & lit, HowChanged how) {
        overloaded{
            [](const TrueLiteral &) {},
            [](const FalseLiteral &) {},
            [&](const IntegerVariableCondition & cond) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) { requeue_variable(var, how); },
                    [&](const ViewOfIntegerVariableID & var) { requeue_variable(var.actual_variable, how); },
                    [](const ConstantIntegerVariableID &) {}}
                    .visit(cond.var);
            }}
            .visit(lit);
    };

    if (start_from_guess_rather_than_all_propagators)
        requeue_literal(start_from_guess_rather_than_all_propagators->first, start_from_guess_rather_than_all_propagators->second);
    else {
        for (unsigned i = 0; i < _imp->propagation_functions.size(); ++i) {
            queue.push_back(i);
            on_queue.emplace(i);
        }
    }

    bool contradiction = false;
    visit([&](auto && inference) -> void {
        while ((! contradiction) && (! queue.empty())) {
            int propagator_id = *queue.begin();
            queue.erase(queue.begin());
            on_queue.erase(propagator_id);

            try {
                auto propagator_state = overloaded{
                    [&](PropagationFunction & f) -> PropagatorState {
                        return f(state, inference);
                    },
                    [&](EagerPropagationFunction & f) {
                        return inference.run_in_eager_mode([&](auto & eager_inference) -> PropagatorState {
                            return f(state, logger, eager_inference);
                        });
                    }}.visit(_imp->propagation_functions.at(propagator_id));
                ++_imp->total_propagations;

                for (const auto & [literal, how_changed] : inference.changes) {
                    ++_imp->effectful_propagations;
                    requeue_literal(literal, how_changed);
                }
                inference.changes.clear();

                switch (propagator_state) {
                case PropagatorState::Enable:
                    break;
                case PropagatorState::DisableUntilBacktrack:
                    disabled.insert(propagator_id);
                    break;
                }
            }
            catch (const TrackedPropagationFailed &) {
                contradiction = true;
                ++_imp->contradicting_propagations;
                inference.changes.clear();
                break;
            }

            if (optional_abort_flag && optional_abort_flag->load())
                contradiction = true;
        }

        if constexpr (std::is_same_v<std::decay_t<decltype(inference)>, LazyProofGenerationInferenceTracker>) {
            inference.for_each_pending_proof_step([&](const Literal & lit, const Justification & just, const Reason & why) {
                inference.logger.infer(state, false, lit, just, why);
            });
        }
    },
        inference);

#if 0
    state.on_backtrack([&, orig_idle_end = orig_idle_end]() {
        _imp->idle_end = orig_idle_end;
    });
#endif

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
                    (1 << static_cast<int>(HowChanged::InteriorValuesChanged)) |
                    (1 << static_cast<int>(HowChanged::BoundsChanged)) |
                    (1 << static_cast<int>(HowChanged::Instantiated)));
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
                    (1 << static_cast<int>(HowChanged::BoundsChanged)) |
                    (1 << static_cast<int>(HowChanged::Instantiated)));
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
                    (1 << static_cast<int>(HowChanged::Instantiated)));
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
