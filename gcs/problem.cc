#include <gcs/constraints/in.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/presolver.hh>
#include <gcs/problem.hh>

#include <gcs/constraints/linear.hh>

#include <util/overloaded.hh>

#include <deque>
#include <tuple>

using namespace gcs;
using namespace gcs::innards;

using std::deque;
using std::function;
using std::make_optional;
using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::string;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::vector;

struct Problem::Imp
{
    State initial_state{};
    deque<unique_ptr<Constraint>> constraints{};
    deque<tuple<SimpleIntegerVariableID, Integer, Integer, optional<string>>> integer_variables{};
    deque<unique_ptr<Presolver>> presolvers{};
    vector<IntegerVariableID> problem_variables{};
    optional<IntegerVariableID> optional_minimise_variable{};
};

Problem::Problem() :
    _imp(new Imp{})
{
}

Problem::~Problem() = default;

auto Problem::create_integer_variable(Integer lower, Integer upper,
    const optional<string> & name) -> SimpleIntegerVariableID
{
    if (lower > upper)
        throw UnexpectedException{"variable has lower bound > upper bound"};

    auto result = _imp->initial_state.allocate_integer_variable_with_state(lower, upper);
    _imp->integer_variables.emplace_back(result, lower, upper, name);
    _imp->problem_variables.push_back(result);
    return result;
}

auto Problem::create_integer_variable(const vector<Integer> & domain, const optional<string> & name) -> SimpleIntegerVariableID
{
    if (domain.empty())
        throw UnexpectedException{"variable has empty domain"};

    auto [min, max] = minmax_element(domain.begin(), domain.end());

    auto result = _imp->initial_state.allocate_integer_variable_with_state(*min, *max);
    _imp->integer_variables.emplace_back(result, *min, *max, name);
    _imp->problem_variables.push_back(result);

    post(In{result, domain});

    return result;
}

auto Problem::create_integer_variable_vector(
    size_t how_many,
    Integer lower,
    Integer upper,
    const optional<string> & name) -> vector<IntegerVariableID>
{
    vector<IntegerVariableID> result;
    result.reserve(how_many);
    for (size_t n = 0; n < how_many; ++n)
        result.push_back(create_integer_variable(lower, upper, name ? make_optional(*name + to_string(n)) : nullopt));
    return result;
}

auto Problem::create_state_for_new_search(
    ProofModel * const model) const -> State
{
    auto result = _imp->initial_state.clone();
    if (model) {
        for (auto & [id, lower, upper, optional_name] : _imp->integer_variables)
            model->set_up_integer_variable(id, lower, upper, optional_name, nullopt);
    }
    return result;
}

auto Problem::post(const Constraint & c) -> void
{
    _imp->constraints.push_back(c.clone());
}

auto Problem::post(SumLessEqual<Weighted<IntegerVariableID>> expr) -> void
{
    post(LinearLessEqual(move(expr.lhs), expr.rhs));
}

auto Problem::post(SumEquals<Weighted<IntegerVariableID>> expr) -> void
{
    post(LinearEquality(move(expr.lhs), expr.rhs));
}

auto Problem::add_presolver(const Presolver & p) -> void
{
    _imp->presolvers.push_back(p.clone());
}

auto Problem::create_propagators(State & state, ProofModel * const optional_proof_model) const -> Propagators
{
    Propagators result;
    for (auto & c : _imp->constraints) {
        auto cc = c->clone();
        move(*cc).install(result, state, optional_proof_model);
    }

    return result;
}

auto Problem::for_each_presolver(const function<auto(Presolver &)->bool> & f) const -> bool
{
    for (auto & p : _imp->presolvers)
        if (! f(*p))
            return false;

    return true;
}

auto Problem::minimise(IntegerVariableID var) -> void
{
    _imp->optional_minimise_variable = var;
}

auto Problem::maximise(IntegerVariableID var) -> void
{
    _imp->optional_minimise_variable = -var;
}

auto Problem::optional_minimise_variable() const -> optional<IntegerVariableID>
{
    return _imp->optional_minimise_variable;
}

auto Problem::all_normal_variables() const -> const vector<IntegerVariableID> &
{
    return _imp->problem_variables;
}
