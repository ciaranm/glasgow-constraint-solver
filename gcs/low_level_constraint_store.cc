/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/low_level_constraint_store.hh>
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

struct LowLevelConstraintStore::Imp
{
    Problem * const problem;
    list<Literals> cnfs;
    deque<PropagationFunction> propagation_functions;
    vector<tuple<microseconds, unsigned long long, string> > propagation_function_calls;
    microseconds total_propagation_time{ 0 };
    unsigned long long total_propagations = 0;
    deque<vector<int> > iv_triggers;

    Imp(Problem * p) :
        problem(p)
    {
    }
};

LowLevelConstraintStore::LowLevelConstraintStore(Problem * p) :
    _imp(new Imp(p))
{
    _imp->propagation_functions.emplace_back([&] (State & s) { return propagate_cnfs(s); });
    _imp->propagation_function_calls.emplace_back(microseconds{ 0 }, 0, "cnf");
}

LowLevelConstraintStore::~LowLevelConstraintStore() = default;

auto LowLevelConstraintStore::trim_lower_bound(const State & state, IntegerVariableID var, Integer val) -> void
{
    if (state.lower_bound(var) < val) {
        if (state.upper_bound(var) >= val)
            cnf(state, { var >= val }, true);
        else
            cnf(state, { }, true);
    }
}

auto LowLevelConstraintStore::trim_upper_bound(const State & state, IntegerVariableID var, Integer val) -> void
{
    if (state.upper_bound(var) > val) {
        if (state.lower_bound(var) <= val + 1_i)
            cnf(state, { var < val + 1_i }, true);
        else
            cnf(state, { }, true);
    }
}

auto LowLevelConstraintStore::cnf(const State &, Literals && c, bool propagating) -> optional<ProofLine>
{
    optional<ProofLine> result = nullopt;

    if (sanitise_literals(c)) {
        if (_imp->problem->optional_proof())
            result = _imp->problem->optional_proof()->cnf(c);

        if (propagating)
            _imp->cnfs.emplace_back(move(c));
    }

    return result;
}

auto LowLevelConstraintStore::at_most_one(const State &, Literals && lits, bool propagating) -> optional<ProofLine>
{
    if (propagating)
        throw UnimplementedException{ };

    if (_imp->problem->optional_proof())
        return _imp->problem->optional_proof()->at_most_one(move(lits));
    else
        return nullopt;
}

auto LowLevelConstraintStore::pseudoboolean_ge(const State &, WeightedLiterals && lits, Integer val, bool propagating) -> std::optional<ProofLine>
{
    if (propagating)
        throw UnimplementedException{ };

    if (_imp->problem->optional_proof())
        return _imp->problem->optional_proof()->pseudoboolean_ge(lits, val);
    else
        return nullopt;
}

auto LowLevelConstraintStore::integer_linear_le(const State & state, Linear && coeff_vars, Integer value) -> void
{
    sanitise_linear(coeff_vars);

    if (_imp->problem->optional_proof())
        _imp->problem->optional_proof()->integer_linear_le(state, coeff_vars, value);

    int id = _imp->propagation_functions.size();
    for (auto & [ _, v ] : coeff_vars)
        add_trigger(v, id);

    _imp->propagation_functions.emplace_back([&, coeff_vars = move(coeff_vars), value = value] (State & state) -> Inference {
            return propagate_linear(coeff_vars, value, state);
    });

    _imp->propagation_function_calls.emplace_back(microseconds{ 0 }, 0, "int_lin_le");
}

auto LowLevelConstraintStore::propagator(const State &, PropagationFunction && f, const vector<VariableID> & trigger_vars, const std::string & name) -> void
{
    int id = _imp->propagation_functions.size();
    _imp->propagation_functions.emplace_back(move(f));
    _imp->propagation_function_calls.emplace_back(microseconds{ 0 }, 0, name);
    for (auto & t : trigger_vars)
        add_trigger(t, id);
}

auto LowLevelConstraintStore::table(const State & state, vector<IntegerVariableID> && vars, vector<vector<Integer> > && permitted, const std::string & name) -> void
{
    if (permitted.empty()) {
        cnf(state, { }, true);
        return;
    }

    int id = _imp->propagation_functions.size();
    auto selector = create_auxilliary_integer_variable(0_i, Integer(permitted.size() - 1), "table", false);

    // pb encoding, if necessary
    if (want_nonpropagating()) {
        for_each_with_index(permitted, [&] (const auto & tuple, auto tuple_idx) {
                // selector == tuple_idx -> /\_i vars[i] == tuple[i]
                WeightedLiterals lits;
                lits.emplace_back(Integer(tuple.size()), selector != Integer(tuple_idx));
                for_each_with_index(vars, [&] (IntegerVariableID var, auto var_idx) {
                        lits.emplace_back(1_i, var == tuple[var_idx]);
                });
                pseudoboolean_ge(state, move(lits), Integer(tuple.size()), false);
            });
    }

    // set up triggers before we move vars away
    for (auto & t : vars)
        add_trigger(t, id);

    _imp->propagation_functions.emplace_back([&, table = ExtensionalData{ selector, move(vars), move(permitted) }] (State & state) -> Inference {
            return propagate_extensional(table, state);
            });
    _imp->propagation_function_calls.emplace_back(microseconds{ 0 }, 0, name);
}

auto LowLevelConstraintStore::propagate(State & state) const -> bool
{
    vector<int> on_queue(_imp->propagation_functions.size(), 0);
    deque<int> propagation_queue;

    while (true) {
        state.extract_changed_variables([&] (VariableID var) {
                visit(overloaded{
                        [&] (const IntegerVariableID & ivar) {
                            visit(overloaded{
                                    [&] (const unsigned long long idx) {
                                        if (idx < _imp->iv_triggers.size())
                                            for (auto & p : _imp->iv_triggers[idx])
                                                if (! on_queue[p]) {
                                                    propagation_queue.push_back(p);
                                                    on_queue[p] = 1;
                                                }
                                    },
                                    [&] (const Integer) {
                                        throw UnimplementedException{ };
                                    }
                                }, ivar.index_or_const_value);
                        },
                        [&] (const BooleanVariableID &) {
                            throw UnimplementedException{ };
                        }
                        }, var);

                if ((! _imp->cnfs.empty()) && ! on_queue[0]) {
                    propagation_queue.push_back(0);
                    on_queue[0] = 1;
                }
                });

        if (propagation_queue.empty())
            break;

        int propagator_id = *propagation_queue.begin();
        propagation_queue.erase(propagation_queue.begin());
        on_queue[propagator_id] = 0;
        auto start_time = steady_clock::now();
        auto inference = _imp->propagation_functions[propagator_id](state);
        auto tm = duration_cast<microseconds>(steady_clock::now() - start_time);
        get<0>(_imp->propagation_function_calls[propagator_id]) += tm;
        get<1>(_imp->propagation_function_calls[propagator_id])++;
        _imp->total_propagation_time += tm;
        _imp->total_propagations++;
        switch (inference) {
            case Inference::NoChange:      break;
            case Inference::Change:        break;
            case Inference::Contradiction: return false;
        }
    }

    return true;
}

auto LowLevelConstraintStore::propagate_cnfs(State & state) const -> Inference
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

auto LowLevelConstraintStore::create_auxilliary_integer_variable(Integer l, Integer u, const std::string & s, bool need_ge) -> IntegerVariableID
{
    return _imp->problem->create_integer_variable(l, u, make_optional("aux_" + s), need_ge);
}

auto LowLevelConstraintStore::want_nonpropagating() const -> bool
{
    return _imp->problem->optional_proof() != nullopt;
}

auto LowLevelConstraintStore::fill_in_constraint_stats(Stats & stats) const -> void
{
    stats.n_cnfs += _imp->cnfs.size();
    stats.n_propagators += _imp->propagation_functions.size();
    stats.propagation_function_calls = _imp->propagation_function_calls;
    stats.propagation_function_calls.emplace_back(_imp->total_propagation_time, _imp->total_propagations, "totals");
}

auto LowLevelConstraintStore::add_trigger(VariableID var, int t) -> void
{
    visit(overloaded{
            [&] (const IntegerVariableID & ivar) {
                visit(overloaded{
                        [&] (const unsigned long long idx) {
                            if (_imp->iv_triggers.size() <= idx)
                                    _imp->iv_triggers.resize(idx + 1);
                            _imp->iv_triggers[idx].push_back(t);
                        },
                        [&] (const Integer) {
                        }
                        }, ivar.index_or_const_value);
            },
            [&] (const BooleanVariableID &) {
                throw UnimplementedException{ };
            }
            }, var);
}

