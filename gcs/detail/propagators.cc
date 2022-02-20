/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>

#include <gcs/detail/extensional.hh>
#include <gcs/detail/linear_utils.hh>
#include <gcs/detail/proof.hh>
#include <gcs/detail/propagators.hh>

#include <util/for_each.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <chrono>
#include <deque>
#include <list>

using namespace gcs;

using std::deque;
using std::list;
using std::make_optional;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::vector;
using std::chrono::microseconds;

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
    Problem * const problem;
    list<Literals> cnfs;
    list<Literal> unary_cnfs;
    deque<PropagationFunction> propagation_functions;
    vector<uint8_t> propagator_is_disabled;
    microseconds total_propagation_time{0};
    unsigned long long total_propagations = 0, effectful_propagations = 0, contradicting_propagations = 0;
    deque<TriggerIDs> iv_triggers;
    bool first = true;

    Imp(Problem * p) :
        problem(p)
    {
    }
};

Propagators::Propagators(Problem * p) :
    _imp(new Imp(p))
{
}

Propagators::~Propagators() = default;

auto Propagators::model_contradiction(const State & initial_state, const string & explain_yourself) -> void
{
    if (_imp->problem->optional_proof())
        _imp->problem->optional_proof()->cnf({});

    install(
        initial_state, [explain_yourself = explain_yourself](State &) -> pair<Inference, PropagatorState> {
            return pair{Inference::Contradiction, PropagatorState::Enable};
        },
        Triggers{}, "model contradiction");
}

auto Propagators::trim_lower_bound(const State & state, IntegerVariableID var, Integer val, const string & x) -> void
{
    if (state.lower_bound(var) < val) {
        if (state.upper_bound(var) >= val) {
            define_cnf(state, {var >= val});
            install(
                state, [var, val](State & state) {
                    return pair{state.infer(var >= val, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                },
                Triggers{}, "trimmed lower bound");
        }
        else
            model_contradiction(state, "Trimmed lower bound of " + debug_string(var) + " due to " + x + " is outside its domain");
    }
}

auto Propagators::trim_upper_bound(const State & state, IntegerVariableID var, Integer val, const string & x) -> void
{
    if (state.upper_bound(var) > val) {
        if (state.lower_bound(var) <= val) {
            define_cnf(state, {var < val + 1_i});
            install(
                state, [var, val](State & state) {
                    return pair{state.infer(var < val + 1_i, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                },
                Triggers{}, "trimmed upper bound");
        }
        else
            model_contradiction(state, "Trimmed upper bound of " + debug_string(var) + " due to " + x + " is outside its domain");
    }
}

auto Propagators::define_cnf(const State &, Literals && c) -> optional<ProofLine>
{
    optional<ProofLine> result = nullopt;

    if (_imp->problem->optional_proof())
        if (sanitise_literals(c))
            result = _imp->problem->optional_proof()->cnf(c);

    return result;
}

auto Propagators::define_at_most_one(const State &, Literals && lits) -> optional<ProofLine>
{
    if (_imp->problem->optional_proof())
        return _imp->problem->optional_proof()->at_most_one(move(lits));
    else
        return nullopt;
}

auto Propagators::define_pseudoboolean_ge(const State &, WeightedLiterals && lits, Integer val) -> optional<ProofLine>
{
    if (_imp->problem->optional_proof())
        return _imp->problem->optional_proof()->pseudoboolean_ge(lits, val);
    else
        return nullopt;
}

auto Propagators::define_linear_le(const State & state, const Linear & coeff_vars,
    Integer value, optional<LiteralFromIntegerVariableOrProofFlag> half_reif) -> optional<ProofLine>
{
    if (_imp->problem->optional_proof()) {
        auto [cv, modifier] = simplify_linear(coeff_vars);
        return _imp->problem->optional_proof()->integer_linear_le(state, cv, value + modifier, half_reif, false);
    }
    else
        return nullopt;
}

auto Propagators::define_linear_eq(const State & state, const Linear & coeff_vars,
    Integer value, optional<LiteralFromIntegerVariableOrProofFlag> half_reif) -> optional<ProofLine>
{
    if (_imp->problem->optional_proof()) {
        auto [cv, modifier] = simplify_linear(coeff_vars);
        return _imp->problem->optional_proof()->integer_linear_le(state, cv, value + modifier, half_reif, true);
    }
    else
        return nullopt;
}

auto Propagators::install(const State &, PropagationFunction && f, const Triggers & triggers, const std::string &) -> void
{
    int id = _imp->propagation_functions.size();
    _imp->propagation_functions.emplace_back(move(f));
    _imp->propagator_is_disabled.push_back(0);

    for (const auto & v : triggers.on_change)
        trigger_on_change(v, id);
    for (const auto & v : triggers.on_bounds)
        trigger_on_bounds(v, id);
    for (const auto & v : triggers.on_instantiated)
        trigger_on_instantiated(v, id);
}

auto Propagators::define_and_install_table(const State & state, vector<IntegerVariableID> && vars,
        vector<vector<Integer>> && permitted, const string & x) -> void
{
    if (permitted.empty()) {
        model_contradiction(state, "Empty table constraint from " + x);
        return;
    }

    int id = _imp->propagation_functions.size();
    auto selector = create_auxilliary_integer_variable(0_i, Integer(permitted.size() - 1), "table");

    // pb encoding, if necessary
    if (want_definitions()) {
        for_each_with_index(permitted, [&](const auto & tuple, auto tuple_idx) {
            // selector == tuple_idx -> /\_i vars[i] == tuple[i]
            bool infeasible = false;
            WeightedLiterals lits;
            lits.emplace_back(Integer(tuple.size()), selector != Integer(tuple_idx));
            for_each_with_index(vars, [&](IntegerVariableID var, auto var_idx) {
                if (is_literally_false(var == tuple[var_idx]))
                    infeasible = true;
                else if (! is_literally_true(var == tuple[var_idx]))
                    lits.emplace_back(1_i, var == tuple[var_idx]);
            });
            if (infeasible)
                define_cnf(state, {selector != Integer(tuple_idx)});
            else
                define_pseudoboolean_ge(state, move(lits), Integer(lits.size() - 1));
        });
    }

    // set up triggers before we move vars away
    for (auto & v : vars)
        trigger_on_change(v, id);
    trigger_on_change(selector, id);

    _imp->propagation_functions.emplace_back([&, table = ExtensionalData{selector, move(vars), move(permitted)}](
                                                 State & state) -> pair<Inference, PropagatorState> {
        return propagate_extensional(table, state);
    });
    _imp->propagator_is_disabled.push_back(0);
}

auto Propagators::propagate(State & state, const optional<IntegerVariableID> & objective_variable,
    const optional<Integer> & objective_value) const -> bool
{
    vector<int> on_queue(_imp->propagation_functions.size(), 0);
    deque<int> propagation_queue;
    vector<int> newly_disabled_propagators;
    newly_disabled_propagators.reserve(_imp->propagation_functions.size());

    if (objective_variable && objective_value) {
        switch (state.infer(*objective_variable < *objective_value, NoJustificationNeeded{})) {
        case Inference::NoChange: break;
        case Inference::Change: break;
        case Inference::Contradiction: return false;
        }
    }

    if (_imp->first) {
        _imp->first = false;
        for (unsigned i = 0; i != _imp->propagation_functions.size(); ++i) {
            propagation_queue.push_back(i);
            on_queue[i] = 1;
        }

        for (auto & lit : _imp->unary_cnfs)
            switch (state.infer(lit, NoJustificationNeeded{})) {
            case Inference::Contradiction: return false;
            case Inference::NoChange: break;
            case Inference::Change: break;
            }
    }

    bool contradiction = false;
    while (! contradiction) {
        if (propagation_queue.empty()) {
            state.extract_changed_variables([&](SimpleIntegerVariableID v, HowChanged h) {
                if (v.index < _imp->iv_triggers.size()) {
                    auto & triggers = _imp->iv_triggers[v.index];

                    // the 0 == (on_queue + is_disabled) thing is to turn two branches into
                    // one, and is really saying (! on_queue && ! is_disabled). annoyingly,
                    // this is a hotspot in some benchmarks...

                    for (auto & p : triggers.on_change)
                        if (0 == (on_queue[p] + _imp->propagator_is_disabled[p])) {
                            propagation_queue.push_back(p);
                            on_queue[p] = 1;
                        }

                    if (h != HowChanged::InteriorValuesChanged)
                        for (auto & p : triggers.on_bounds)
                            if (0 == (on_queue[p] + _imp->propagator_is_disabled[p])) {
                                propagation_queue.push_back(p);
                                on_queue[p] = 1;
                            }

                    if (h == HowChanged::Instantiated)
                        for (auto & p : triggers.on_instantiated)
                            if (0 == (on_queue[p] + _imp->propagator_is_disabled[p])) {
                                propagation_queue.push_back(p);
                                on_queue[p] = 1;
                            }
                }
            });
        }

        if (propagation_queue.empty())
            break;

        int propagator_id = propagation_queue.front();
        propagation_queue.pop_front();
        on_queue[propagator_id] = 0;
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
                if (0 == _imp->propagator_is_disabled[propagator_id]) {
                    _imp->propagator_is_disabled[propagator_id] = 1;
                    newly_disabled_propagators.push_back(propagator_id);
                }
                break;
            }
        }
    }

    if (! newly_disabled_propagators.empty()) {
        state.on_backtrack([&, to_enable = move(newly_disabled_propagators)]() {
            for (const auto & p : to_enable)
                _imp->propagator_is_disabled[p] = 0;
        });
    }

    return ! contradiction;
}

auto Propagators::create_auxilliary_integer_variable(Integer l, Integer u, const std::string & s) -> IntegerVariableID
{
    return _imp->problem->create_integer_variable(l, u, make_optional("aux_" + s));
}

auto Propagators::create_proof_flag(const std::string & n) -> ProofFlag
{
    if (! _imp->problem->optional_proof())
        throw UnexpectedException{"trying to create a proof flag but proof logging is not enabled"};
    return _imp->problem->optional_proof()->create_proof_flag(n);
}

auto Propagators::want_definitions() const -> bool
{
    return _imp->problem->optional_proof() != nullopt;
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
