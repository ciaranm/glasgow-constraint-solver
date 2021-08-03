/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/problem.hh"
#include "gcs/exception.hh"
#include "gcs/state.hh"
#include "gcs/low_level_constraint_store.hh"

#include "util/for_each.hh"
#include "util/overloaded.hh"

using namespace gcs;

using std::make_optional;
using std::move;
using std::nullopt;
using std::optional;
using std::vector;

struct Problem::Imp
{
    State initial_state;
    optional<IntegerVariableID> last_integer_var;
    LowLevelConstraintStore constraints;
    optional<vector<IntegerVariableID> > branch_on;

    Imp(Problem * problem) :
        constraints(problem)
    {
    }
};

Problem::Problem() :
    _imp(new Imp(this))
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

    if (_imp->branch_on) {
        for (auto & var : *_imp->branch_on) {
            Integer s = state.domain_size(var);
            if (s > Integer{ 1 } && (nullopt == result || s < sz)) {
                result = var;
                sz = s;
            }
        }
    }
    else if (_imp->last_integer_var) {
        for (IntegerVariableID var{ 0 } ; var <= *_imp->last_integer_var ; ++std::get<unsigned long long>(var.index_or_const_value)) {
            Integer s = state.domain_size(var);
            if (s > Integer{ 1 } && (nullopt == result || s < sz)) {
                result = var;
                sz = s;
            }
        }
    }

    return result;
}

auto Problem::post(Constraint && c) -> void
{
    move(c).convert_to_low_level(_imp->constraints, initial_state());
}

auto Problem::branch_on(const std::vector<IntegerVariableID> & v) -> void
{
    if (! _imp->branch_on)
        _imp->branch_on.emplace();
    _imp->branch_on->insert(_imp->branch_on->end(), v.begin(), v.end());
}

