/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/low_level_constraint_store.hh>
#include <gcs/exception.hh>
#include <gcs/extensional.hh>
#include <util/overloaded.hh>
#include <util/for_each.hh>

#include <algorithm>
#include <chrono>
#include <list>
#include <map>
#include <set>

using namespace gcs;

using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;
using std::list;
using std::make_optional;
using std::map;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::vector;

struct LowLevelConstraintStore::Imp
{
    Problem * const problem;
    list<Literals> cnfs;
    map<int, PropagationFunction> propagation_functions;
    vector<microseconds> propagation_function_times;
    map<VariableID, vector<int> > triggers;

    Imp(Problem * p) :
        problem(p)
    {
    }
};

LowLevelConstraintStore::LowLevelConstraintStore(Problem * p) :
    _imp(new Imp(p))
{
    _imp->propagation_functions.emplace(0, [&] (State & s) { return propagate_cnfs(s); });
    _imp->propagation_function_times.emplace_back();
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
        _imp->triggers.try_emplace(v).first->second.push_back(id);

    _imp->propagation_functions.emplace(id, [&, coeff_vars = move(coeff_vars), value = value] (State & state) -> Inference {
            return propagate_linear(coeff_vars, value, state);
    });

    _imp->propagation_function_times.emplace_back();
}

auto LowLevelConstraintStore::propagator(const State &, PropagationFunction && f, const vector<VariableID> & trigger_vars) -> void
{
    int id = _imp->propagation_functions.size();
    _imp->propagation_functions.emplace(id, move(f));
    _imp->propagation_function_times.emplace_back();
    for (auto & t : trigger_vars)
        _imp->triggers.try_emplace(t).first->second.push_back(id);
}

auto LowLevelConstraintStore::table(const State & state, vector<IntegerVariableID> && vars, vector<vector<Integer> > && permitted) -> void
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
        _imp->triggers.try_emplace(t).first->second.push_back(id);

    _imp->propagation_functions.emplace(id, [&, table = ExtensionalData{ selector, move(vars), move(permitted) }] (State & state) -> Inference {
            return propagate_extensional(table, state);
            });
    _imp->propagation_function_times.emplace_back();
}

auto LowLevelConstraintStore::propagate(State & state) const -> bool
{
    set<int> propagation_queue;

    while (true) {
        if (propagation_queue.empty())
            state.extract_changed_variables([&] (VariableID var) {
                    auto t = _imp->triggers.find(var);
                    if (t != _imp->triggers.end())
                        for (auto & p : t->second)
                            propagation_queue.insert(p);
                    propagation_queue.insert(0);
                    });

        if (propagation_queue.empty())
            break;

        int propagator_id = *propagation_queue.begin();
        propagation_queue.erase(propagation_queue.begin());
        auto start_time = steady_clock::now();
        auto inference = _imp->propagation_functions.find(propagator_id)->second(state);
        _imp->propagation_function_times[propagator_id] += duration_cast<microseconds>(steady_clock::now() - start_time);
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
        Literals nonfalsified_literals;

        for (auto & lit : clause) {
            if (visit(overloaded {
                        [&] (const LiteralFromBooleanVariable & blit) -> bool {
                            auto single_value = state.optional_single_value(blit.var);
                            if (! single_value)
                                throw UnimplementedException{ };
                            return *single_value == (blit.state == LiteralFromBooleanVariable::True);
                        },
                        [&] (const LiteralFromIntegerVariable & ilit) -> bool {
                            switch (ilit.state) {
                                case LiteralFromIntegerVariable::Equal:
                                    return state.in_domain(ilit.var, ilit.value);
                                case LiteralFromIntegerVariable::Less:
                                    return state.lower_bound(ilit.var) < ilit.value;
                                case LiteralFromIntegerVariable::GreaterEqual:
                                     return state.upper_bound(ilit.var) >= ilit.value;
                                case LiteralFromIntegerVariable::NotEqual: {
                                    auto single_value = state.optional_single_value(ilit.var);
                                    return (nullopt == single_value || *single_value != ilit.value);
                                }
                            }

                            throw NonExhaustiveSwitch{ };
                        }
                        }, lit))
                nonfalsified_literals.push_back(lit);

            if (nonfalsified_literals.size() >= 2)
                break;
        }

        if (nonfalsified_literals.size() == 0)
            return Inference::Contradiction;
        else if (nonfalsified_literals.size() == 1) {
            switch (state.infer(nonfalsified_literals[0], NoJustificationNeeded{ })) {
                case Inference::Contradiction: return Inference::Contradiction;
                case Inference::NoChange:      break;
                case Inference::Change:        changed = true; break;
            }
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
    stats.propagation_function_times = _imp->propagation_function_times;
}

