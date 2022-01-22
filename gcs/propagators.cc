/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/propagators.hh>
#include <gcs/exception.hh>
#include <gcs/extensional.hh>
#include <util/overloaded.hh>
#include <util/for_each.hh>

#include <algorithm>
#include <chrono>
#include <deque>
#include <list>

using namespace gcs;

using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;
using std::deque;
using std::get;
using std::list;
using std::make_optional;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::tuple;
using std::vector;

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
    microseconds total_propagation_time{ 0 };
    unsigned long long total_propagations = 0;
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
    _imp->propagation_functions.emplace_back([&] (State & s) { return pair{ propagate_cnfs(s), PropagatorState::Enable }; });
    _imp->propagator_is_disabled.push_back(0);
}

Propagators::~Propagators() = default;

auto Propagators::trim_lower_bound(const State & state, IntegerVariableID var, Integer val) -> void
{
    if (state.lower_bound(var) < val) {
        if (state.upper_bound(var) >= val)
            cnf(state, { var >= val }, true);
        else
            cnf(state, { }, true);
    }
}

auto Propagators::trim_upper_bound(const State & state, IntegerVariableID var, Integer val) -> void
{
    if (state.upper_bound(var) > val) {
        if (state.lower_bound(var) <= val + 1_i)
            cnf(state, { var < val + 1_i }, true);
        else
            cnf(state, { }, true);
    }
}

auto Propagators::cnf(const State &, Literals && c, bool propagating) -> optional<ProofLine>
{
    optional<ProofLine> result = nullopt;

    if (sanitise_literals(c)) {
        if (_imp->problem->optional_proof())
            result = _imp->problem->optional_proof()->cnf(c);

        if (propagating) {
            if (c.size() == 1)
                _imp->unary_cnfs.push_back(*c.begin());
            else
                _imp->cnfs.emplace_back(move(c));
        }
    }

    return result;
}

auto Propagators::at_most_one(const State &, Literals && lits, bool propagating) -> optional<ProofLine>
{
    if (propagating)
        throw UnimplementedException{ };

    if (_imp->problem->optional_proof())
        return _imp->problem->optional_proof()->at_most_one(move(lits));
    else
        return nullopt;
}

auto Propagators::pseudoboolean_ge(const State &, WeightedLiterals && lits, Integer val, bool propagating) -> std::optional<ProofLine>
{
    if (propagating)
        throw UnimplementedException{ };

    if (_imp->problem->optional_proof())
        return _imp->problem->optional_proof()->pseudoboolean_ge(lits, val);
    else
        return nullopt;
}

auto Propagators::integer_linear_le(const State & state, Linear && coeff_vars, Integer value, bool equality) -> void
{
    sanitise_linear(coeff_vars);

    optional<ProofLine> proof_line;
    if (_imp->problem->optional_proof())
        proof_line = _imp->problem->optional_proof()->integer_linear_le(state, coeff_vars, value, equality);

    int id = _imp->propagation_functions.size();
    for (auto & [ _, v ] : coeff_vars)
        trigger_on_bounds(v, id);

    _imp->propagation_functions.emplace_back([&, coeff_vars = move(coeff_vars), value = value,
            equality = equality, proof_line = proof_line] (State & state) {
            return propagate_linear(coeff_vars, value, state, equality, proof_line);
    });
    _imp->propagator_is_disabled.push_back(0);
}

auto Propagators::propagator(const State &, PropagationFunction && f, const Triggers & triggers, const std::string &) -> void
{
    int id = _imp->propagation_functions.size();
    _imp->propagation_functions.emplace_back(move(f));
    _imp->propagator_is_disabled.push_back(0);

    for (auto & v : triggers.on_change)
        trigger_on_change(v, id);
    for (auto & v : triggers.on_bounds)
        trigger_on_bounds(v, id);
    for (auto & v : triggers.on_instantiated)
        trigger_on_instantiated(v, id);
}

auto Propagators::table(const State & state, vector<IntegerVariableID> && vars, vector<vector<Integer> > && permitted, const std::string &) -> void
{
    if (permitted.empty()) {
        cnf(state, { }, true);
        return;
    }

    int id = _imp->propagation_functions.size();
    auto selector = create_auxilliary_integer_variable(0_i, Integer(permitted.size() - 1), "table");

    // pb encoding, if necessary
    if (want_nonpropagating()) {
        for_each_with_index(permitted, [&] (const auto & tuple, auto tuple_idx) {
                // selector == tuple_idx -> /\_i vars[i] == tuple[i]
                bool infeasible = false;
                WeightedLiterals lits;
                lits.emplace_back(Integer(tuple.size()), selector != Integer(tuple_idx));
                for_each_with_index(vars, [&] (IntegerVariableID var, auto var_idx) {
                    if (is_literally_false(var == tuple[var_idx]))
                        infeasible = true;
                    else if (! is_literally_true(var == tuple[var_idx]))
                        lits.emplace_back(1_i, var == tuple[var_idx]);
                });
                if (infeasible)
                    cnf(state, { selector != Integer(tuple_idx) }, true);
                else
                    pseudoboolean_ge(state, move(lits), Integer(lits.size() - 1), false);
            });
    }

    // set up triggers before we move vars away
    for (auto & v : vars)
        trigger_on_change(v, id);
    trigger_on_change(selector, id);

    _imp->propagation_functions.emplace_back([&, table = ExtensionalData{ selector, move(vars), move(permitted) }] (
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

    if (objective_variable && objective_value) {
        switch (state.infer(*objective_variable < *objective_value, NoJustificationNeeded{ })) {
            case Inference::NoChange:      break;
            case Inference::Change:        break;
            case Inference::Contradiction: return false;
        }
    }

    if (_imp->first) {
        _imp->first = false;
        for (unsigned i = 0 ; i != _imp->propagation_functions.size() ; ++i) {
            propagation_queue.push_back(i);
            on_queue[i] = 1;
        }

        for (auto & lit : _imp->unary_cnfs)
            switch (state.infer(lit, NoJustificationNeeded{ })) {
                case Inference::Contradiction: return false;
                case Inference::NoChange:      break;
                case Inference::Change:        break;
            }
    }

    bool contradiction = false;
    while (! contradiction) {
        if (propagation_queue.empty()) {
            state.extract_changed_variables([&] (SimpleIntegerVariableID v, HowChanged h) {
                if (v.index < _imp->iv_triggers.size()) {
                    auto & triggers = _imp->iv_triggers[v.index];
                    for (auto & p : triggers.on_change)
                        if (! on_queue[p] && ! _imp->propagator_is_disabled[p]) {
                            propagation_queue.push_back(p);
                            on_queue[p] = 1;
                        }

                    if (! triggers.on_bounds.empty() && h != HowChanged::InteriorValuesChanged)
                        for (auto & p : triggers.on_bounds)
                            if (! on_queue[p] && ! _imp->propagator_is_disabled[p]) {
                                propagation_queue.push_back(p);
                                on_queue[p] = 1;
                            }

                    if (! triggers.on_instantiated.empty() && h == HowChanged::Instantiated)
                        for (auto & p : triggers.on_instantiated)
                            if (! on_queue[p] && ! _imp->propagator_is_disabled[p]) {
                                propagation_queue.push_back(p);
                                on_queue[p] = 1;
                            }
                }

                if ((! _imp->cnfs.empty()) && ! on_queue[0]) {
                    propagation_queue.push_back(0);
                    on_queue[0] = 1;
                }
                });
        }

        if (propagation_queue.empty())
            break;

        int propagator_id = *propagation_queue.begin();
        propagation_queue.erase(propagation_queue.begin());
        on_queue[propagator_id] = 0;
        auto [ inference, propagator_state ] = _imp->propagation_functions[propagator_id](state);
        ++_imp->total_propagations;
        switch (inference) {
            case Inference::NoChange:      break;
            case Inference::Change:        break;
            case Inference::Contradiction: contradiction = true; break;
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
        state.on_backtrack([&, to_enable = move(newly_disabled_propagators)] () {
                for (auto & p : to_enable)
                    _imp->propagator_is_disabled[p] = 0;
            });
    }

    return ! contradiction;
}

auto Propagators::propagate_cnfs(State & state) const -> Inference
{
    bool changed = false;

    for (auto & clause : _imp->cnfs) {
        Literals::iterator nonfalsified_literal_1 = clause.end(), nonfalsified_literal_2 = clause.end();

        for (auto lit = clause.begin(), lit_end = clause.end() ; lit != lit_end ; ++lit) {
            if (state.literal_is_nonfalsified(*lit)) {
                if (nonfalsified_literal_1 == clause.end())
                    nonfalsified_literal_1 = lit;
                else {
                    nonfalsified_literal_2 = lit;
                    break;
                }
            }
        }

        if (nonfalsified_literal_1 == clause.end())
            return Inference::Contradiction;
        else if (nonfalsified_literal_2 == clause.end()) {
            swap(*nonfalsified_literal_1, clause[0]);
            switch (state.infer(clause[0], NoJustificationNeeded{ })) {
                case Inference::Contradiction: return Inference::Contradiction;
                case Inference::NoChange:      break;
                case Inference::Change:        changed = true; break;
            }
        }
        else {
            swap(*nonfalsified_literal_1, clause[0]);
            swap(*nonfalsified_literal_2, clause[1]);
        }
    }

    return changed ? Inference::Change : Inference::NoChange;
}

auto Propagators::create_auxilliary_integer_variable(Integer l, Integer u, const std::string & s) -> IntegerVariableID
{
    return _imp->problem->create_integer_variable(l, u, make_optional("aux_" + s));
}

auto Propagators::want_nonpropagating() const -> bool
{
    return _imp->problem->optional_proof() != nullopt;
}

auto Propagators::fill_in_constraint_stats(Stats & stats) const -> void
{
    stats.n_cnfs += _imp->cnfs.size();
    stats.n_propagators += _imp->propagation_functions.size();
    stats.propagations += _imp->total_propagations;
}

auto Propagators::trigger_on_change(VariableID var, int t) -> void
{
    visit(overloaded{
            [&] (const IntegerVariableID & ivar) {
                visit(overloaded{
                        [&] (const SimpleIntegerVariableID & v) {
                            if (_imp->iv_triggers.size() <= v.index)
                                    _imp->iv_triggers.resize(v.index + 1);
                            _imp->iv_triggers[v.index].on_change.push_back(t);
                        },
                        [&] (const ViewOfIntegerVariableID & v) {
                            trigger_on_change(v.actual_variable, t);
                        },
                        [&] (const ConstantIntegerVariableID &) {
                        }
                        }, ivar);
            }
            }, var);
}

auto Propagators::trigger_on_bounds(VariableID var, int t) -> void
{
    visit(overloaded{
            [&] (const IntegerVariableID & ivar) {
                visit(overloaded{
                        [&] (const SimpleIntegerVariableID & v) {
                            if (_imp->iv_triggers.size() <= v.index)
                                    _imp->iv_triggers.resize(v.index + 1);
                            _imp->iv_triggers[v.index].on_bounds.push_back(t);
                        },
                        [&] (const ViewOfIntegerVariableID & v) {
                            trigger_on_bounds(v.actual_variable, t);
                        },
                        [&] (const ConstantIntegerVariableID &) {
                        }
                        }, ivar);
            }
            }, var);
}

auto Propagators::trigger_on_instantiated(VariableID var, int t) -> void
{
    visit(overloaded{
            [&] (const IntegerVariableID & ivar) {
                visit(overloaded{
                        [&] (const SimpleIntegerVariableID & v) {
                            if (_imp->iv_triggers.size() <= v.index)
                                    _imp->iv_triggers.resize(v.index + 1);
                            _imp->iv_triggers[v.index].on_instantiated.push_back(t);
                        },
                        [&] (const ViewOfIntegerVariableID & v) {
                            trigger_on_instantiated(v.actual_variable, t);
                        },
                        [&] (const ConstantIntegerVariableID &) {
                        }
                        }, ivar);
            }
            }, var);
}

