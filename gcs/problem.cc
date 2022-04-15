/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/in.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::make_optional;
using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::string;
using std::to_string;
using std::vector;

struct Problem::Imp
{
    State initial_state;
    Propagators propagators;
    vector<SimpleIntegerVariableID> problem_variables;
    optional<vector<SimpleIntegerVariableID>> branch_on;
    optional<IntegerVariableID> objective_variable;
    optional<Integer> objective_value;
    optional<Proof> optional_proof;

    Imp(Problem * problem) :
        initial_state(problem),
        propagators(problem)
    {
    }
};

Problem::Problem() :
    _imp(new Imp(this))
{
}

Problem::Problem(const ProofOptions & options) :
    _imp(new Imp(this))
{
    _imp->optional_proof = make_optional<Proof>(options);
}

Problem::~Problem() = default;

auto Problem::create_integer_variable(Integer lower, Integer upper, const optional<std::string> & name) -> SimpleIntegerVariableID
{
    if (lower > upper)
        throw UnexpectedException{"variable has lower bound > upper bound"};

    auto result = _imp->initial_state.create_integer_variable(lower, upper);
    _imp->problem_variables.push_back(result);
    if (_imp->optional_proof)
        _imp->optional_proof->create_integer_variable(result, lower, upper, name);
    return result;
}

auto Problem::create_integer_variable(const vector<Integer> & domain, const optional<std::string> & name) -> SimpleIntegerVariableID
{
    if (domain.empty())
        throw UnexpectedException{"variable has empty domain"};

    auto [min, max] = minmax_element(domain.begin(), domain.end());

    auto result = _imp->initial_state.create_integer_variable(*min, *max);
    _imp->problem_variables.push_back(result);
    if (_imp->optional_proof)
        _imp->optional_proof->create_integer_variable(result, *min, *max, name);

    post(In{result, domain});

    return result;
}

auto Problem::create_integer_variable_vector(
    size_t how_many,
    Integer lower,
    Integer upper,
    const optional<string> & name) -> std::vector<IntegerVariableID>
{
    vector<IntegerVariableID> result;
    result.reserve(how_many);
    for (size_t n = 0; n < how_many; ++n)
        result.push_back(create_integer_variable(lower, upper, name ? make_optional(*name + to_string(n)) : nullopt));
    return result;
}

auto Problem::create_state() const -> State
{
    return _imp->initial_state.clone();
}

auto Problem::propagate(State & state, atomic<bool> * optional_abort_flag) const -> bool
{
    auto result = _imp->propagators.propagate(state, _imp->objective_variable, _imp->objective_value, optional_abort_flag);

    return result;
}

auto Problem::find_branching_variable(State & state) const -> optional<IntegerVariableID>
{
    optional<IntegerVariableID> result = nullopt;
    Integer sz{0};

    for (auto & var : (_imp->branch_on ? *_imp->branch_on : _imp->problem_variables)) {
        Integer s = state.domain_size(var);
        if (s > Integer{1} && (nullopt == result || s < sz)) {
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
    move(c).install(_imp->propagators, _imp->initial_state);
}

auto Problem::branch_on(const std::vector<IntegerVariableID> & vars) -> void
{
    if (! _imp->branch_on)
        _imp->branch_on.emplace();

    for (auto & v : vars)
        overloaded{
            [&](const SimpleIntegerVariableID & v) { _imp->branch_on->push_back(v); },
            [&](const ViewOfIntegerVariableID & v) { _imp->branch_on->push_back(v.actual_variable); },
            [&](const ConstantIntegerVariableID &) {}}
            .visit(v);
}

auto Problem::optional_proof() const -> std::optional<Proof> &
{
    return _imp->optional_proof;
}

auto Problem::minimise(IntegerVariableID var) -> void
{
    if (_imp->objective_variable)
        throw UnexpectedException{"not sure how to have multiple objective variables"};
    _imp->objective_variable = var;

    if (_imp->optional_proof)
        _imp->optional_proof->minimise(var);
}

auto Problem::maximise(IntegerVariableID var) -> void
{
    if (_imp->objective_variable)
        throw UnexpectedException{"not sure how to have multiple objective variables"};
    _imp->objective_variable = -var;

    if (_imp->optional_proof)
        _imp->optional_proof->minimise(-var);
}

auto Problem::update_objective(const State & state) -> void
{
    if (_imp->objective_variable)
        _imp->objective_value = state(*_imp->objective_variable);
}

auto Problem::fill_in_constraint_stats(Stats & stats) const -> void
{
    _imp->propagators.fill_in_constraint_stats(stats);
}
