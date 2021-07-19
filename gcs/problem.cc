/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/problem.hh"
#include "gcs/exception.hh"
#include "gcs/state.hh"

#include "util/for_each.hh"
#include "util/overloaded.hh"

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
using std::to_string;
using std::vector;

struct LowLevelConstraintStore::Imp
{
    list<Literals> cnfs;
    list<pair<Linear, Integer> > lin_les;
};

LowLevelConstraintStore::LowLevelConstraintStore() :
    _imp(new Imp)
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

struct Problem::Imp
{
    State initial_state;
    optional<IntegerVariableID> last_integer_var;
    LowLevelConstraintStore constraints;
};

Problem::Problem() :
    _imp(new Imp)
{
}

Problem::~Problem()
{
}

auto Problem::initial_state() -> State &
{
    return _imp->initial_state;
}

auto Problem::initial_state() const -> const State &
{
    return _imp->initial_state;
}

auto Problem::create_integer_variable(Integer lower, Integer upper) -> IntegerVariableID
{
    return *(_imp->last_integer_var = make_optional(initial_state().create_integer_variable(lower, upper)));
}

auto Problem::create_integer_offset_variable(IntegerVariableID var, Integer offset) -> IntegerVariableID
{
    return *(_imp->last_integer_var = make_optional(initial_state().create_integer_offset_variable(var, offset)));
}

auto Problem::create_integer_constant(Integer value) -> IntegerVariableID
{
    return *(_imp->last_integer_var = make_optional(initial_state().create_integer_variable(value, value)));
}

auto Problem::create_boolean_constant(bool value) -> BooleanVariableID
{
    return initial_state().create_boolean_constant(value);
}

auto Problem::create_initial_state() const -> State
{
    return initial_state().clone();
}

auto Problem::propagate(State & state) const -> bool
{
    auto result = _imp->constraints.propagate(state);

    return result;
}

auto Problem::find_branching_variable(State & state) const -> optional<IntegerVariableID>
{
    optional<IntegerVariableID> result = nullopt;
    Integer sz{ 0 };

    if (_imp->last_integer_var)
        for (IntegerVariableID var{ 0 } ; var <= *_imp->last_integer_var ; ++var.index) {
            Integer s = state.domain_size(var);
            if (s > Integer{ 1 } && (nullopt == result || s < sz)) {
                result = var;
                sz = s;
            }
        }

    return result;
}

auto Problem::post(Constraint && c) -> void
{
    move(c).convert_to_low_level(_imp->constraints, initial_state());
}

