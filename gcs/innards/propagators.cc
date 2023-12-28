#include <gcs/exception.hh>

#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/linear_utils.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <bit>
#include <chrono>
#include <list>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::bit_ceil;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::swap;
using std::vector;
using std::visit;

namespace
{
    struct TriggerIDs
    {
        vector<int> on_change;
        vector<int> on_bounds;
        vector<int> on_instantiated;
    };
}

struct Propagators::Imp
{
    optional<Proof> & optional_proof;

    vector<PropagationFunction> propagation_functions;
    vector<InitialisationFunction> initialisation_functions;

    // Every propagation function's index appears exactly once in queue, and lookup[id] always tells
    // us where that position is. The items from index 0 to enqueued_end - 1 are ready to be
    // propagated, and the items between enqueued_end and idle_end - 1 do not need to be propagated.
    // Anything from idle_end onwards is disabled until backtrack. If anything funky happens, such
    // as new propagators being added, setting first to true will re-initialise the queue the next
    // time propagation occurs.
    vector<int> queue, lookup;
    int enqueued_end, idle_end;

    unsigned long long total_propagations = 0, effectful_propagations = 0, contradicting_propagations = 0;
    vector<TriggerIDs> iv_triggers;
    vector<long> degrees;
    bool first = true;

    Imp(optional<Proof> & o) :
        optional_proof(o)
    {
    }
};

Propagators::Propagators(optional<Proof> & o) :
    _imp(new Imp(o))
{
}

Propagators::~Propagators() = default;

Propagators::Propagators(Propagators &&) = default;

auto Propagators::operator=(Propagators &&) -> Propagators & = default;

auto Propagators::model_contradiction(const string & explain_yourself) -> void
{
    if (_imp->optional_proof)
        _imp->optional_proof->add_cnf_to_model({});

    install([explain_yourself = explain_yourself](State &) -> pair<Inference, PropagatorState> {
        return pair{Inference::Contradiction, PropagatorState::Enable};
    },
        Triggers{}, "model contradiction");
}

auto Propagators::trim_lower_bound(const State & state, IntegerVariableID var, Integer val, const string & x) -> void
{
    if (state.lower_bound(var) < val) {
        if (state.upper_bound(var) >= val) {
            define_cnf(state, {var >= val});
            install([var, val](State & state) {
                return pair{state.infer(var >= val, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
            },
                Triggers{}, "trimmed lower bound");
        }
        else
            model_contradiction("Trimmed lower bound of " + debug_string(var) + " due to " + x + " is outside its domain");
    }
}

auto Propagators::trim_upper_bound(const State & state, IntegerVariableID var, Integer val, const string & x) -> void
{
    if (state.upper_bound(var) > val) {
        if (state.lower_bound(var) <= val) {
            define_cnf(state, {var < val + 1_i});
            install([var, val](State & state) {
                return pair{state.infer(var < val + 1_i, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
            },
                Triggers{}, "trimmed upper bound");
        }
        else
            model_contradiction("Trimmed upper bound of " + debug_string(var) + " due to " + x + " is outside its domain");
    }
}

auto Propagators::define_cnf(const State &, const Literals & c) -> optional<ProofLine>
{
    if (_imp->optional_proof)
        return _imp->optional_proof->add_cnf_to_model(c);
    else
        return nullopt;
}

auto Propagators::define(const State &, const WeightedPseudoBooleanLessEqual & ineq,
    const optional<HalfReifyOnConjunctionOf> & half_reif) -> optional<ProofLine>
{
    if (_imp->optional_proof)
        return _imp->optional_proof->add_to_model(ineq, half_reif);
    else
        return nullopt;
}

auto Propagators::define(const State &, const WeightedPseudoBooleanEquality & eq,
    const optional<HalfReifyOnConjunctionOf> & half_reif) -> pair<optional<ProofLine>, optional<ProofLine>>
{
    if (_imp->optional_proof)
        return _imp->optional_proof->add_to_model(eq, half_reif);
    else
        return pair{nullopt, nullopt};
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

auto Propagators::define_and_install_table(State & state, const vector<IntegerVariableID> & vars,
    ExtensionalTuples permitted, const string & x) -> void
{
    visit([&](auto && permitted) {
        if (depointinate(permitted).empty()) {
            model_contradiction("Empty table constraint from " + x);
            return;
        }

        int id = _imp->propagation_functions.size();
        auto selector = create_auxilliary_integer_variable(state, 0_i, Integer(depointinate(permitted).size() - 1), "table",
            IntegerVariableProofRepresentation::DirectOnly);

        // pb encoding, if necessary
        if (want_definitions()) {
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
                    define_cnf(state, {selector != Integer(tuple_idx)});
                else
                    define(state, lits >= Integer(lits.terms.size() - 1));
            }
        }

        // set up triggers before we move vars away
        for (auto & v : vars)
            trigger_on_change(v, id);
        trigger_on_change(selector, id);

        _imp->propagation_functions.emplace_back([&, table = ExtensionalData{selector, move(vars), move(permitted)}](
                                                     State & state) -> pair<Inference, PropagatorState> {
            return propagate_extensional(table, state);
        });
    },
        move(permitted));
}

auto Propagators::initialise(State & state) const -> void
{
    for (auto & f : _imp->initialisation_functions)
        f(state);
}

auto Propagators::requeue_all_propagators() -> void
{
    _imp->first = true;
}

auto Propagators::propagate(State & state, atomic<bool> * optional_abort_flag) const -> bool
{
    switch (state.infer_on_objective_variable_before_propagation()) {
    case Inference::NoChange: break;
    case Inference::Change: break;
    case Inference::Contradiction: return false;
    }

    if (_imp->first) {
        // filthy hack: to make trim_lower_bound etc work, on the first pass, we need to
        // guarantee that we're running propagators in numerical order, except our queue
        // runs backwards so we need to put them in backwards.
        _imp->first = false;
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
    else
        _imp->enqueued_end = 0;

    auto orig_idle_end = _imp->idle_end;

    bool contradiction = false;
    while (! contradiction) {
        if (0 == _imp->enqueued_end) {
            state.extract_changed_variables([&](SimpleIntegerVariableID v, HowChanged h) {
                if (v.index < _imp->iv_triggers.size()) {
                    auto & triggers = _imp->iv_triggers[v.index];

                    if (h == HowChanged::Instantiated)
                        for (auto & p : triggers.on_instantiated)
                            if (_imp->lookup[p] >= _imp->enqueued_end && _imp->lookup[p] < _imp->idle_end) {
                                auto being_swapped_item = _imp->queue[_imp->enqueued_end];
                                swap(_imp->queue[_imp->lookup[p]], _imp->queue[_imp->enqueued_end]);
                                swap(_imp->lookup[p], _imp->lookup[being_swapped_item]);
                                ++_imp->enqueued_end;
                            }

                    if (h != HowChanged::InteriorValuesChanged)
                        for (auto & p : triggers.on_bounds)
                            if (_imp->lookup[p] >= _imp->enqueued_end && _imp->lookup[p] < _imp->idle_end) {
                                auto being_swapped_item = _imp->queue[_imp->enqueued_end];
                                swap(_imp->queue[_imp->lookup[p]], _imp->queue[_imp->enqueued_end]);
                                swap(_imp->lookup[p], _imp->lookup[being_swapped_item]);
                                ++_imp->enqueued_end;
                            }

                    for (auto & p : triggers.on_change)
                        if (_imp->lookup[p] >= _imp->enqueued_end && _imp->lookup[p] < _imp->idle_end) {
                            auto being_swapped_item = _imp->queue[_imp->enqueued_end];
                            swap(_imp->queue[_imp->lookup[p]], _imp->queue[_imp->enqueued_end]);
                            swap(_imp->lookup[p], _imp->lookup[being_swapped_item]);
                            ++_imp->enqueued_end;
                        }
                }
            });
        }

        if (0 == _imp->enqueued_end)
            break;

        int propagator_id = _imp->queue[--_imp->enqueued_end];
        auto [inference, propagator_state] = _imp->propagation_functions[propagator_id](state);
        ++_imp->total_propagations;
        switch (inference) {
        case Inference::NoChange:
            break;
        case Inference::Change:
            ++_imp->effectful_propagations;
            break;
        case Inference::Contradiction:
            ++_imp->contradicting_propagations;
            contradiction = true;
            break;
        }

        if (! contradiction) {
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

        if (optional_abort_flag && optional_abort_flag->load())
            return false;
    }


    state.on_backtrack([&, orig_idle_end = orig_idle_end]() {
        _imp->idle_end = orig_idle_end;
    });

    return ! contradiction;
}

auto Propagators::create_auxilliary_integer_variable(State & state, Integer l, Integer u, const std::string & s,
    const IntegerVariableProofRepresentation rep) -> IntegerVariableID
{
    auto result = state.allocate_integer_variable_with_state(l, u);
    if (_imp->optional_proof)
        _imp->optional_proof->set_up_integer_variable(result, l, u, "aux_" + s, rep);
    return result;
}

auto Propagators::create_proof_flag(const std::string & n) -> ProofFlag
{
    if (! _imp->optional_proof)
        throw UnexpectedException{"trying to create a proof flag but proof logging is not enabled"};
    return _imp->optional_proof->create_proof_flag(n);
}

auto Propagators::create_proof_only_integer_variable(Integer l, Integer u, const std::string & s,
    const IntegerVariableProofRepresentation rep) -> ProofOnlySimpleIntegerVariableID
{
    if (! _imp->optional_proof)
        throw UnexpectedException{"trying to create a proof variable but proof logging is not enabled"};
    return _imp->optional_proof->create_proof_integer_variable(l, u, s, rep);
}

auto Propagators::want_definitions() const -> bool
{
    return _imp->optional_proof != nullopt;
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
            _imp->iv_triggers[v.index].on_change.push_back(t);
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
            _imp->iv_triggers[v.index].on_bounds.push_back(t);
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
            _imp->iv_triggers[v.index].on_instantiated.push_back(t);
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
