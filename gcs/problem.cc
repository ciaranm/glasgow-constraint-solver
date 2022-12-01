/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/in.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>

#include <util/overloaded.hh>

#include <list>

using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::list;
using std::make_optional;
using std::make_shared;
using std::make_unique;
using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

struct Problem::Imp
{
    optional<Proof> optional_proof;
    State initial_state;
    list<unique_ptr<Constraint>> constraints;
    vector<IntegerVariableID> problem_variables;

    Imp(const ProofOptions * optional_options) :
        optional_proof(optional_options ? optional<Proof>{*optional_options} : nullopt),
        initial_state(optional_proof ? &*optional_proof : nullptr)
    {
    }
};

Problem::Problem() :
    _imp(new Imp{nullptr})
{
}

Problem::Problem(const ProofOptions & options) :
    _imp(new Imp{&options})
{
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

auto Problem::post(const Constraint & c) -> void
{
    _imp->constraints.push_back(c.clone());
}

auto Problem::create_propagators(State & state) -> Propagators
{
    auto result = Propagators{state, optional_proof()};
    for (auto & c : _imp->constraints) {
        auto cc = c->clone();
        if (optional_proof())
            optional_proof()->posting(cc->describe_for_proof());
        move(*cc).install(result, state);
    }

    return result;
}

auto Problem::optional_proof() const -> std::optional<Proof> &
{
    return _imp->optional_proof;
}

auto Problem::minimise(IntegerVariableID var) -> void
{
    _imp->initial_state.minimise(var);
}

auto Problem::maximise(IntegerVariableID var) -> void
{
    _imp->initial_state.maximise(var);
}

auto Problem::all_normal_variables() const -> const std::vector<IntegerVariableID> &
{
    return _imp->problem_variables;
}
