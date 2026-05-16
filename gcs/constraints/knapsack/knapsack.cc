#include <gcs/constraints/knapsack/knapsack.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <sstream>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::optional;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

Knapsack::Knapsack(vector<Integer> weights, vector<Integer> profits,
    vector<IntegerVariableID> vars, IntegerVariableID weight, IntegerVariableID profit) :
    _coeffs({move(weights), move(profits)}),
    _vars(move(vars)),
    _totals({weight, profit})
{
}

Knapsack::Knapsack(vector<vector<Integer>> coefficients,
    vector<IntegerVariableID> vars,
    vector<IntegerVariableID> totals) :
    _coeffs(move(coefficients)),
    _vars(move(vars)),
    _totals(move(totals))
{
}

auto Knapsack::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Knapsack>(_coeffs, _vars, _totals);
}

auto Knapsack::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Knapsack::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    if (_coeffs.size() != _totals.size())
        throw InvalidProblemDefinitionException{"Knapsack: coefficients and totals must have the same number of equations"};
    if (_coeffs.empty())
        throw InvalidProblemDefinitionException{"Knapsack: at least one equation is required"};

    auto n_vars = _coeffs.front().size();
    for (const auto & c : _coeffs)
        if (c.size() != n_vars)
            throw InvalidProblemDefinitionException{"Knapsack: every coefficient row must have the same length"};
    if (n_vars != _vars.size())
        throw InvalidProblemDefinitionException{"Knapsack: coefficient row length must match number of variables"};

    for (const auto & cc : _coeffs)
        for (const auto & c : cc)
            if (c < 0_i)
                throw InvalidProblemDefinitionException{"Knapsack: coefficients must be non-negative"};

    for (const auto & v : _vars)
        if (initial_state.lower_bound(v) < 0_i)
            throw InvalidProblemDefinitionException{"Knapsack: item variables must be non-negative"};

    for (const auto & t : _totals)
        if (initial_state.lower_bound(t) < 0_i)
            throw InvalidProblemDefinitionException{"Knapsack: total variables must be non-negative"};

    return true;
}

auto Knapsack::define_proof_model(ProofModel & model) -> void
{
    // Natural definition: one linear equality per total.
    //   sum_i coeffs[x][i] * vars[i] == totals[x]
    // The DAG-shaped propagator scaffolding (Stage 2) sits on top of
    // these equations; nothing about the propagator's algorithm leaks
    // into this declarative encoding.
    for (const auto & [cc_idx, cc] : enumerate(_coeffs)) {
        WPBSum sum_eq;
        for (const auto & [idx, v] : enumerate(_vars))
            sum_eq += cc.at(idx) * v;
        model.add_constraint(move(sum_eq) == 1_i * _totals.at(cc_idx));
    }
}

auto Knapsack::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};
    triggers.on_change.insert(triggers.on_change.end(), _totals.begin(), _totals.end());

    // Stage 1: all-fixed checker. When every item is single-valued,
    // each totals[x] is forced to the computed sum via RUP from the
    // natural per-equation OPB constraint plus the assigned-item
    // literals. Mid-search pruning is Stage 2.
    propagators.install(
        [coeffs = _coeffs, vars = _vars, totals = _totals](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            vector<Integer> single_values;
            single_values.reserve(vars.size());
            for (const auto & v : vars) {
                auto sv = state.optional_single_value(v);
                if (! sv)
                    return PropagatorState::Enable;
                single_values.push_back(*sv);
            }

            Reason all_vars_assigned;
            all_vars_assigned.reserve(vars.size());
            for (const auto & [idx, v] : enumerate(vars))
                all_vars_assigned.emplace_back(v == single_values.at(idx));

            for (const auto & [x, total] : enumerate(totals)) {
                Integer sum = 0_i;
                for (const auto & [idx, _] : enumerate(vars))
                    sum += coeffs.at(x).at(idx) * single_values.at(idx);
                inference.infer(logger, total == sum, JustifyUsingRUP{},
                    [r = all_vars_assigned]() { return r; });
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Knapsack::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} knapsack\n            (", _name);
    for (const auto & cs : _coeffs) {
        print(s, "\n                (");
        for (const auto & c : cs)
            print(s, " {}", c);
        print(s, ")");
    }
    print(s, "\n            )\n            (");
    for (const auto & v : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, ")\n            (");
    for (const auto & t : _totals)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(t));
    print(s, ")\n        ");

    return s.str();
}
