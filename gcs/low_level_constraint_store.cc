/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/low_level_constraint_store.hh"
#include "gcs/exception.hh"
#include "util/overloaded.hh"
#include "util/for_each.hh"

#include <algorithm>
#include <list>
#include <map>
#include <set>

using namespace gcs;

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
    list<pair<Linear, Integer> > lin_les;
    map<int, PropagationFunction> propagation_functions;
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
    _imp->propagation_functions.emplace(1, [&] (State & s) { return propagate_lin_les(s); });
}

LowLevelConstraintStore::~LowLevelConstraintStore() = default;

auto LowLevelConstraintStore::cnf(Literals && c, bool propagating) -> void
{
    sanitise_literals(c);
    if (_imp->problem->optional_proof())
        _imp->problem->optional_proof()->cnf(c);

    if (propagating)
        _imp->cnfs.emplace_back(move(c));
}

auto LowLevelConstraintStore::lin_le(Linear && coeff_vars, Integer value) -> void
{
    sanitise_linear(coeff_vars);
    _imp->lin_les.emplace_back(move(coeff_vars), value);
}

auto LowLevelConstraintStore::propagator(PropagationFunction && f, const vector<VariableID> & trigger_vars) -> void
{
    int id = _imp->propagation_functions.size();
    _imp->propagation_functions.emplace(id, move(f));
    for (auto & t : trigger_vars)
        _imp->triggers.try_emplace(t).first->second.push_back(id);
}

auto LowLevelConstraintStore::table(vector<IntegerVariableID> && vars, vector<vector<Integer> > && permitted) -> void
{
    int id = _imp->propagation_functions.size();

    // set up triggers before we move vars away
    for (auto & t : vars)
        _imp->triggers.try_emplace(t).first->second.push_back(id);

    _imp->propagation_functions.emplace(id, [&, table = Table{ create_auxilliary_integer_variable(0_i, Integer(permitted.size() - 1), "table", false), move(vars), move(permitted) }] (State & state) -> Inference {
            return propagate_table(table, state);
            });
}

auto LowLevelConstraintStore::propagate(State & state) const -> bool
{
    set<int> propagation_queue;

    while (true) {
        state.extract_changed_variables([&] (VariableID var) {
                auto t = _imp->triggers.find(var);
                if (t != _imp->triggers.end())
                    for (auto & p : t->second)
                        propagation_queue.insert(p);

                propagation_queue.emplace(0);
                propagation_queue.emplace(1);
                propagation_queue.emplace(2);
                });

        if (propagation_queue.empty())
            break;

        int propagator_id = *propagation_queue.begin();
        propagation_queue.erase(propagation_queue.begin());
        switch (_imp->propagation_functions.find(propagator_id)->second(state)) {
            case Inference::NoChange:      break;
            case Inference::Change:        break;
            case Inference::Contradiction: return false;
        }
    }

    return true;
}

auto LowLevelConstraintStore::propagate_table(const Table & table, State & state) const -> Inference
{
    bool changed = false, contradiction = false;

    // check whether selectable tuples are still feasible
    for_each_with_index(table.tuples, [&] (const auto & tuple, auto tuple_idx) {
        if ((! contradiction) && state.in_domain(table.selector, Integer(tuple_idx))) {
            bool is_feasible = true;
            for_each_with_index(table.vars, [&] (IntegerVariableID var, auto idx) {
                    if (! state.in_domain(var, tuple[idx]))
                        is_feasible = false;
                    });
            if (! is_feasible) {
                switch (state.infer(table.selector != Integer(tuple_idx), Justification::Assert)) {
                    case Inference::NoChange:      break;
                    case Inference::Change:        changed = true; break;
                    case Inference::Contradiction: contradiction = true; break;
                }
            }
        }
    });

    if (contradiction)
        return Inference::Contradiction;

    // check for supports in selectable tuples
    for_each_with_index(table.vars, [&] (IntegerVariableID var, auto idx) {
            state.for_each_value(var, [&] (Integer val) {
                    bool supported = false;
                    for_each_with_index(table.tuples, [&] (const auto & tuple, auto tuple_idx) {
                            if (state.in_domain(table.selector, Integer(tuple_idx)) && tuple[idx] == val)
                                supported = true;
                            });

                    if (! supported) {
                        switch (state.infer(var != val, Justification::Assert)) {
                            case Inference::NoChange:      break;
                            case Inference::Change:        changed = true; break;
                            case Inference::Contradiction: contradiction = true; break;
                        }
                    }
                });
        });

    return contradiction ? Inference::Contradiction : changed ? Inference::Change : Inference::NoChange;
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
            switch (state.infer(nonfalsified_literals[0], Justification::RUP)) {
                case Inference::Contradiction: return Inference::Contradiction;
                case Inference::NoChange:      break;
                case Inference::Change:        changed = true; break;
            }
        }
    }

    return changed ? Inference::Change : Inference::NoChange;
}

auto LowLevelConstraintStore::propagate_lin_les(State & state) const -> Inference
{
    bool changed = false;

    for (auto & ineq : _imp->lin_les) {
        Integer lower{ 0 };

        for (auto & [ coeff, var ] : ineq.first)
            lower += (coeff >= 0_i) ? (coeff * state.lower_bound(var)) : (coeff * state.upper_bound(var));

        // Feasibility check: if each variable takes its best value, can we satisfy the inequality?
        if (lower > ineq.second)
            return Inference::Contradiction;
    }

    for (auto & ineq : _imp->lin_les) {
        // Propagation: what's the worst value a variable can take, if every
        // other variable is given its best value?
        for (auto & [ coeff, var ] : ineq.first) {
            Integer lower_without_me{ 0 };
            for (auto & [ other_coeff, other_var ] : ineq.first)
                if (var != other_var)
                    lower_without_me += (other_coeff >= 0_i) ? (other_coeff * state.lower_bound(other_var)) : (other_coeff * state.upper_bound(other_var));

            Integer remainder = ineq.second - lower_without_me;
            switch (coeff >= 0_i ? state.infer(var < (1_i + remainder / coeff), Justification::RUP) : state.infer(var >= remainder / coeff, Justification::RUP)) {
                case Inference::Change:        changed = true; break;
                case Inference::NoChange:      break;
                case Inference::Contradiction: return Inference::Contradiction;
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

