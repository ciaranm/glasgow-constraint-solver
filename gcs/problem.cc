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

    list<vector<Literal> > cnfs;
    list<pair<vector<pair<Integer, IntegerVariableID> >, Integer> > lin_les;
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

auto Problem::cnf(vector<Literal> && c) -> void
{
    _imp->cnfs.push_back(move(c));
}

auto Problem::lin_le(std::vector<std::pair<Integer, IntegerVariableID> > & coeff_vars, Integer value) -> void
{
    _imp->lin_les.emplace_back(move(coeff_vars), value);
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
    if (! propagate_cnfs(state))
        return false;

    if (! propagate_lin_les(state))
        return false;

    return true;
}

auto Problem::propagate_cnfs(State & state) const -> bool
{
    for (auto & clause : _imp->cnfs) {
        vector<Literal> nonfalsified_literals;

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
            return false;
        else if (nonfalsified_literals.size() == 1) {
            if (! state.infer(nonfalsified_literals[0]))
                return false;
        }
    }

    return true;
}

auto Problem::propagate_lin_les(State & state) const -> bool
{
    for (auto & ineq : _imp->lin_les) {
        Integer lower{ 0 };

        for (auto & [ coeff, var ] : ineq.first)
            lower += (coeff >= Integer{ 0 }) ? (coeff * lower_bound(state.integer_variable(var))) : (coeff * upper_bound(state.integer_variable(var)));

        if (lower > ineq.second)
            return false;
    }

    return true;
}

auto Problem::find_branching_variable(State & state) const -> std::optional<IntegerVariableID>
{
    if (! _imp->last_integer_var)
        return nullopt;

    for (IntegerVariableID var{ 0 } ; var <= *_imp->last_integer_var ; ++var.index)
        if (nullopt == optional_single_value(state.integer_variable(var)))
            return var;

    return nullopt;
}

