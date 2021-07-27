/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/low_level_constraint_store.hh"
#include "gcs/exception.hh"
#include "util/overloaded.hh"
#include "util/for_each.hh"

#include <algorithm>
#include <list>

using namespace gcs;

using std::list;
using std::make_optional;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::vector;

struct LowLevelConstraintStore::Imp
{
    Problem * const problem;
    list<Literals> cnfs;
    list<pair<Linear, Integer> > lin_les;
    list<PropagationFunction> propagators;

    Imp(Problem * p) :
        problem(p)
    {
    }
};

LowLevelConstraintStore::LowLevelConstraintStore(Problem * p) :
    _imp(new Imp(p))
{
}

LowLevelConstraintStore::~LowLevelConstraintStore() = default;

auto LowLevelConstraintStore::cnf(Literals && c) -> void
{
    sanitise_literals(c);
    _imp->cnfs.push_back(move(c));
}

auto LowLevelConstraintStore::lin_le(Linear && coeff_vars, Integer value) -> void
{
    sanitise_linear(coeff_vars);
    _imp->lin_les.emplace_back(move(coeff_vars), value);
}

auto LowLevelConstraintStore::propagator(PropagationFunction && f) -> void
{
    _imp->propagators.push_back(move(f));
}

auto LowLevelConstraintStore::table(vector<IntegerVariableID> && vars, vector<vector<Integer> > && permitted) -> void
{
    auto selector = create_auxilliary_integer_variable(0_i, Integer(permitted.size() - 1));
    for_each_with_index(permitted, [&] (auto & tuple, auto & pos) {
            if (tuple.size() != vars.size())
                throw UnimplementedException{ };
            for (decltype(tuple.size()) i = 0 ; i != tuple.size() ; ++i)
                cnf({ selector != Integer(pos), vars[i] == tuple[i] });
            });
}

auto LowLevelConstraintStore::propagate(State & state) const -> bool
{
    for (bool keep_going = true ; keep_going ; ) {
        keep_going = false;

        switch (propagate_cnfs(state)) {
            case Inference::NoChange:      break;
            case Inference::Change:        keep_going = true; break;
            case Inference::Contradiction: return false;
        }

        if (keep_going)
            continue;

        switch (propagate_lin_les(state)) {
            case Inference::NoChange:      break;
            case Inference::Change:        keep_going = true; break;
            case Inference::Contradiction: return false;
        }

        if (keep_going)
            continue;

        switch (propagate_propagators(state)) {
            case Inference::NoChange:      break;
            case Inference::Change:        keep_going = true; break;
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
            switch (state.infer(nonfalsified_literals[0])) {
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
            switch (coeff >= 0_i ? state.infer(var < (1_i + remainder / coeff)) : state.infer(var >= remainder / coeff)) {
                case Inference::Change:        changed = true; break;
                case Inference::NoChange:      break;
                case Inference::Contradiction: return Inference::Contradiction;
            }
        }
    }

    return changed ? Inference::Change : Inference::NoChange;
}

auto LowLevelConstraintStore::propagate_propagators(State & state) const -> Inference
{
    bool changed = false;

    for (auto & propagator : _imp->propagators) {
        switch (propagator(state)) {
            case Inference::Change:        changed = true; break;
            case Inference::NoChange:      break;
            case Inference::Contradiction: return Inference::Contradiction;
        }
    }

    return changed ? Inference::Change : Inference::NoChange;
}

auto LowLevelConstraintStore::create_auxilliary_integer_variable(Integer l, Integer u) -> IntegerVariableID
{
    return _imp->problem->create_integer_variable(l, u);
}

