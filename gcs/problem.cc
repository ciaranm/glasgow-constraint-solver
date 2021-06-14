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

auto Problem::initial_state() -> State &
{
    return _imp->initial_state;
}

auto Problem::initial_state() const -> const State &
{
    return _imp->initial_state;
}

auto Problem::allocate_integer_variable(Integer lower, Integer upper) -> IntegerVariableID
{
    return *(_imp->last_integer_var = make_optional(initial_state().allocate_integer_variable(lower, upper)));
}

auto Problem::allocate_integer_offset_variable(IntegerVariableID var, Integer offset) -> IntegerVariableID
{
    return *(_imp->last_integer_var = make_optional(initial_state().allocate_integer_offset_variable(var, offset)));
}

auto Problem::allocate_integer_constant(Integer value) -> IntegerVariableID
{
    return *(_imp->last_integer_var = make_optional(initial_state().allocate_integer_variable(value, value)));
}

auto Problem::allocate_boolean_constant(bool value) -> BooleanVariableID
{
    return initial_state().allocate_boolean_constant(value);
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
            auto lower = max(initial_state().lower_bound(vars[v]), initial_state().lower_bound(vars[w]));
            auto upper = min(initial_state().upper_bound(vars[v]), initial_state().upper_bound(vars[w]));
            for ( ; lower <= upper ; ++lower)
                if (initial_state().in_domain(vars[v], lower) && initial_state().in_domain(vars[w], lower)) {
                    // can't have both variables taking that value
                    cnf({ vars[v] != lower, vars[w] != lower });
                }
        }
}

auto Problem::element(IntegerVariableID var, IntegerVariableID idx_var, const std::vector<IntegerVariableID> & vars) -> void
{
    if (vars.empty()) {
        cnf( { } );
        return;
    }

    // idx_var >= 0, idx_var < vars.size()
    cnf({ idx_var >= 0_i });
    cnf({ idx_var < Integer(vars.size()) });

    // var <= max(upper(vars)), var >= min(lower(vars))
    // ...and this should really be just over vars that idx_var might cover
    auto max_upper = initial_state().upper_bound(*max_element(vars.begin(), vars.end(), [&] (const IntegerVariableID & v, const IntegerVariableID & w) {
                return initial_state().upper_bound(v) < initial_state().upper_bound(w);
                }));
    auto min_lower = initial_state().lower_bound(*min_element(vars.begin(), vars.end(), [&] (const IntegerVariableID & v, const IntegerVariableID & w) {
                return initial_state().lower_bound(v) < initial_state().lower_bound(w);
                }));
    cnf({ var < max_upper + 1_i });
    cnf({ var >= min_lower });

    // for each v in vars
    for (decltype(vars.size()) v = 0 ; v != vars.size() ; ++v) {
        // idx_var == i -> var == vars[i]
        auto lower = min(initial_state().lower_bound(vars[v]), initial_state().lower_bound(var));
        auto upper = max(initial_state().upper_bound(vars[v]), initial_state().upper_bound(var));
        for ( ; lower <= upper ; ++lower) {
            cnf({ idx_var != Integer(v), vars[v] != lower, var == lower });
        }
    }
}

auto Problem::eq_reif(IntegerVariableID v, IntegerVariableID w, BooleanVariableID r) -> void
{
    auto lower_common = max(initial_state().lower_bound(v), initial_state().lower_bound(w));
    auto upper_common = min(initial_state().upper_bound(v), initial_state().upper_bound(w));

    // v < lower_common -> !r, w < lower_common -> !r, v > upper_common -> ! r, w > upper_common -> ! r
    if (initial_state().lower_bound(v) < lower_common)
        cnf({ { v >= lower_common }, { ! r } });
    if (initial_state().lower_bound(w) < lower_common)
        cnf({ { w >= lower_common }, { ! r } });
    if (initial_state().upper_bound(v) > upper_common)
        cnf({ { v < upper_common + 1_i }, { ! r } });
    if (initial_state().upper_bound(w) > upper_common)
        cnf({ { w < upper_common + 1_i }, { ! r } });

    // (r and v == c) -> w == c
    for (auto c = lower_common ; c <= upper_common ; ++c)
        cnf( { { v != c }, { w == c }, { ! r } });

    // (! r and v == c) -> w != c
    for (auto c = lower_common ; c <= upper_common ; ++c)
        cnf( { { + r }, { v != c }, { w != c } } );
}

auto Problem::create_initial_state() const -> State
{
    return initial_state().clone();
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

auto Problem::propagate_lin_les(State & state) const -> Inference
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

