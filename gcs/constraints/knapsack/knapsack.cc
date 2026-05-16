#include <gcs/constraints/knapsack/hints.hh>
#include <gcs/constraints/knapsack/knapsack.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::string;
using std::unique_ptr;
using std::vector;

Knapsack::Knapsack(vector<Integer> weights, vector<Integer> profits, vector<IntegerVariableID> vars, IntegerVariableID weight,
    IntegerVariableID profit) : _coeffs({move(weights), move(profits)}), _vars(move(vars)), _totals({weight, profit})
{
}

Knapsack::Knapsack(vector<vector<Integer>> coefficients, vector<IntegerVariableID> vars, vector<IntegerVariableID> totals) :
    _coeffs(move(coefficients)), _vars(move(vars)), _totals(move(totals))
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
    //
    // cake_pb_cp labels each row's totals equality @c[<id>][<row>_le]/[<row>_ge]:
    // the row index lives in the annotation tag, not the constraint name (a
    // name-embedded row could collide with a sibling constraint's name). Match
    // that so proof steps that cite these lines by label resolve against
    // cake's OPB. Stage 2 will keep the returned lines for the per-call
    // propagator's pol steps; the Stage 1 checker closes by RUP alone.
    for (const auto & [cc_idx, cc] : enumerate(_coeffs)) {
        WPBSum sum_eq;
        for (const auto & [idx, v] : enumerate(_vars))
            sum_eq += cc.at(idx) * v;
        model.add_labelled_constraint(
            constraint_id(), std::to_string(cc_idx) + "_le", std::to_string(cc_idx) + "_ge", sum_eq == 1_i * _totals.at(cc_idx));
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
        constraint_id(),
        [coeffs = _coeffs, vars = _vars, totals = _totals, owner = constraint_id()](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            vector<Integer> single_values;
            single_values.reserve(vars.size());
            for (const auto & v : vars) {
                auto sv = state.optional_single_value(v);
                if (! sv)
                    return PropagatorState::Enable;
                single_values.push_back(*sv);
            }

            ReasonLiterals all_vars_assigned;
            all_vars_assigned.reserve(vars.size());
            for (const auto & [idx, v] : enumerate(vars))
                all_vars_assigned.emplace_back(v == single_values.at(idx));

            for (const auto & [x, total] : enumerate(totals)) {
                Integer sum = 0_i;
                for (const auto & [idx, _] : enumerate(vars))
                    sum += coeffs.at(x).at(idx) * single_values.at(idx);
                inference.infer(logger, total == sum, JustifyUsingRUP{hints::Knapsack{owner}}, all_vars_assigned);
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Knapsack::constraint_type() const -> std::string
{
    return "knapsack";
}

auto Knapsack::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    vector<SExpr> coeff_rows;
    for (const auto & cs : _coeffs) {
        vector<SExpr> row;
        for (const auto & c : cs)
            row.push_back(SExpr::atom(c.to_string()));
        coeff_rows.push_back(SExpr::list(move(row)));
    }

    vector<SExpr> vars;
    for (const auto & v : _vars)
        vars.push_back(tracker.s_expr_term_of(v));

    vector<SExpr> totals;
    for (const auto & t : _totals)
        totals.push_back(tracker.s_expr_term_of(t));

    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(coeff_rows)),
        SExpr::list(move(vars)), SExpr::list(move(totals))});
}
