/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/problem.hh>
#include <gcs/exception.hh>
#include <gcs/state.hh>
#include <gcs/low_level_constraint_store.hh>
#include <gcs/exception.hh>
#include <gcs/constraints/comparison.hh>

#include <util/for_each.hh>
#include <util/overloaded.hh>

using namespace gcs;

using std::make_optional;
using std::move;
using std::nullopt;
using std::optional;
using std::vector;

struct Problem::Imp
{
    State initial_state;
    LowLevelConstraintStore constraints;
    vector<IntegerVariableID> problem_variables;
    optional<vector<IntegerVariableID> > branch_on;
    optional<IntegerVariableID> objective_variable;
    optional<Proof> optional_proof;

    Imp(Problem * problem) :
        initial_state(problem),
        constraints(problem)
    {
    }
};

Problem::Problem() :
    _imp(new Imp(this))
{
}

Problem::Problem(Proof && proof) :
    _imp(new Imp(this))
{
    _imp->optional_proof = move(proof);
}

Problem::~Problem()
{
}

auto Problem::create_integer_variable(Integer lower, Integer upper, const optional<std::string> & name, bool need_ge) -> IntegerVariableID
{
    if (lower > upper)
        throw UnexpectedException{ "variable has lower bound > upper bound" };

    auto result = _imp->initial_state.create_integer_variable(lower, upper);
    _imp->problem_variables.push_back(result);
    if (_imp->optional_proof)
        _imp->optional_proof->create_integer_variable(result, lower, upper, name, need_ge);
    return result;
}

auto Problem::create_state() const -> State
{
    return _imp->initial_state.clone();
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

    for (auto & var : (_imp->branch_on ? *_imp->branch_on : _imp->problem_variables)) {
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
    if (optional_proof())
        optional_proof()->posting(c.describe_for_proof());
    move(c).convert_to_low_level(_imp->constraints, _imp->initial_state);
}

auto Problem::branch_on(const std::vector<IntegerVariableID> & v) -> void
{
    if (! _imp->branch_on)
        _imp->branch_on.emplace();
    _imp->branch_on->insert(_imp->branch_on->end(), v.begin(), v.end());
}

auto Problem::optional_proof() const -> std::optional<Proof> &
{
    return _imp->optional_proof;
}

auto Problem::minimise(IntegerVariableID var) -> void
{
    if (_imp->objective_variable)
        throw UnexpectedException{ "not sure how to have multiple objective variables" };
    _imp->objective_variable = var;

    if (_imp->optional_proof)
        _imp->optional_proof->minimise(var);
}

auto Problem::update_objective(const State & state) -> void
{
    if (_imp->objective_variable)
        post(LessThan{ *_imp->objective_variable, constant_variable(state(*_imp->objective_variable)) });
}

auto Problem::fill_in_constraint_stats(Stats & stats) const -> void
{
    _imp->constraints.fill_in_constraint_stats(stats);
}

