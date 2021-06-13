/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/problem.hh"
#include "gcs/exception.hh"
#include "gcs/state.hh"

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
using std::vector;

struct Problem::Imp
{
    State initial_state;
    optional<IntegerVariableID> last_integer_var;

    list<Literals> cnfs;
    list<pair<Linear, Integer> > lin_les;
};

Problem::Problem() :
    _imp(new Imp)
{
}

Problem::~Problem()
{
}

auto Problem::allocate_integer_variable(Integer lower, Integer upper) -> IntegerVariableID
{
    return *(_imp->last_integer_var = make_optional(_imp->initial_state.allocate_integer_variable(lower, upper)));
}

auto Problem::cnf(Literals && c) -> void
{
    sanitise_literals(c);
    _imp->cnfs.push_back(move(c));
}

auto Problem::lin_le(Linear && coeff_vars, Integer value) -> void
{
    sanitise_linear(coeff_vars);
    _imp->lin_les.emplace_back(move(coeff_vars), value);
}

auto Problem::lin_eq(Linear && coeff_vars, Integer value) -> void
{
    sanitise_linear(coeff_vars);

    // Use input as < constraint, create >= constraint to get equality
    Linear inv_coeff_vars;
    inv_coeff_vars.reserve(coeff_vars.size());
    for (auto & [ c, v ] : coeff_vars)
        inv_coeff_vars.emplace_back(-c, v);

    lin_le(move(inv_coeff_vars), -value);
    lin_le(move(coeff_vars), value);
}

auto Problem::all_different(const vector<IntegerVariableID> & vars) -> void
{
    // for each distinct pair of variables...
    for (decltype(vars.size()) v = 0 ; v < vars.size() ; ++v)
        for (auto w = v + 1 ; w < vars.size() ; ++w) {
            // for each value in both domains...
            auto lower = max(lower_bound(_imp->initial_state.integer_variable(vars[v])), lower_bound(_imp->initial_state.integer_variable(vars[w])));
            auto upper = min(upper_bound(_imp->initial_state.integer_variable(vars[v])), upper_bound(_imp->initial_state.integer_variable(vars[w])));
            for ( ; lower <= upper ; ++lower)
                if (in_domain(_imp->initial_state.integer_variable(vars[v]), lower) && in_domain(_imp->initial_state.integer_variable(vars[w]), lower)) {
                    // can't have both variables taking that value
                    cnf({ vars[v] != lower, vars[w] != lower });
                }
        }
}

auto Problem::create_initial_state() const -> State
{
    return _imp->initial_state.clone();
}

auto Problem::propagate(State & state) const -> bool
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

auto Problem::propagate_cnfs(State & state) const -> Inference
{
    bool changed = false;

    for (auto & clause : _imp->cnfs) {
        Literals nonfalsified_literals;

        for (auto & lit : clause) {
            if (visit(overloaded {
                        [&] (const LiteralFromBooleanVariable &) -> bool { throw UnimplementedException{ }; },
                        [&] (const LiteralFromIntegerVariable & ilit) -> bool {
                            IntegerVariable & var = state.integer_variable(ilit.var);
                            switch (ilit.state) {
                                case LiteralFromIntegerVariable::Equal:
                                    return in_domain(var, ilit.value);
                                case LiteralFromIntegerVariable::Less:
                                    return lower_bound(var) < ilit.value;
                                case LiteralFromIntegerVariable::GreaterEqual:
                                     return upper_bound(var) >= ilit.value;
                                case LiteralFromIntegerVariable::NotEqual: {
                                    auto single_value = optional_single_value(var);
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

auto Problem::propagate_lin_les(State & state) const -> Inference
{
    bool changed = false;

    for (auto & ineq : _imp->lin_les) {
        Integer lower{ 0 };

        for (auto & [ coeff, var ] : ineq.first)
            lower += (coeff >= 0_i) ? (coeff * lower_bound(state.integer_variable(var))) : (coeff * upper_bound(state.integer_variable(var)));

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
                    lower_without_me += (other_coeff >= 0_i) ? (other_coeff * lower_bound(state.integer_variable(other_var))) : (other_coeff * upper_bound(state.integer_variable(other_var)));

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

auto Problem::find_branching_variable(State & state) const -> optional<IntegerVariableID>
{
    optional<IntegerVariableID> result = nullopt;
    Integer sz{ 0 };

    if (_imp->last_integer_var)
        for (IntegerVariableID var{ 0 } ; var <= *_imp->last_integer_var ; ++var.index) {
            Integer s = domain_size(state.integer_variable(var));
            if (s > Integer{ 1 } && (nullopt == result || s < sz)) {
                result = var;
                sz = s;
            }
        }

    return result;
}

