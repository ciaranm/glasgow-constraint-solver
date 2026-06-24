#include <gcs/constraints/n_value/hints.hh>
#include <gcs/constraints/n_value/n_value.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <list>
#include <map>
#include <set>
#include <sstream>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::list;
using std::map;
using std::max;
using std::set;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

NValue::NValue(const IntegerVariableID & n, std::vector<IntegerVariableID> vars) :
    _n_values(n),
    _vars(move(vars))
{
}

auto NValue::clone() const -> unique_ptr<Constraint>
{
    return make_unique<NValue>(_n_values, _vars);
}

auto NValue::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto NValue::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    for (const auto & var : _vars) {
        for (auto v : initial_state.each_value_immutable(var))
            _possible_values.emplace(v, list<IntegerVariableID>{}).first->second.push_back(var);
    }
    return true;
}

auto NValue::define_proof_model(ProofModel & model) -> void
{
    // Conform to cake_pb_cp's nvalue encoding (#354): for each value v in the
    // union of the variables' domains, a fully-reified per-value occurrence flag
    // v[id][v] ⇔ (some var = v) (cake's `elm` / Values), then n_values = the sum
    // of those flags, emitted as cake's c[id][le] / c[id][ge] halves (the same
    // count-sum machinery). The flag's halves are v[id][v][r] (flag -> some
    // var = v) and v[id][v][f] (~flag -> no var = v).
    WPBSum occurrence_sum;
    for (const auto & [v, vars] : _possible_values) {
        WPBSum some_eq;
        for (const auto & var : vars)
            some_eq += 1_i * (var == v);
        auto flag = model.create_proof_flag_values_fully_reifying(_constraint_id, {v.raw_value}, std::nullopt,
            some_eq >= 1_i);
        occurrence_sum += 1_i * flag;
    }
    occurrence_sum += -1_i * _n_values;
    model.add_labelled_constraint(as_string(_constraint_id), "le", "ge",
        "NValue", "sum of occurrence flags", occurrence_sum == 0_i);
}

auto NValue::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_bounds.emplace_back(_n_values);
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());

    vector<IntegerVariableID> all_vars = _vars;
    all_vars.push_back(_n_values);

    propagators.install(constraint_id(), [all_vars = move(all_vars), n_values = _n_values, vars = _vars, owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        set<Integer> all_possible_values;
        for (const auto & var : vars) {
            for (auto v : state.each_value_immutable(var))
                all_possible_values.insert(v);
        }

        inference.infer(logger, n_values <= Integer(all_possible_values.size()), JustifyUsingRUP{hints::NValue{owner}},
            generic_reason(state, all_vars));

        set<Integer> all_definite_values;
        for (const auto & var : vars) {
            auto val = state.optional_single_value(var);
            if (val)
                all_definite_values.insert(*val);
        }

        // The "at least 1" floor only applies when the array is non-empty;
        // an empty array contributes 0 distinct values.
        auto distinct_floor = vars.empty() ? 0_i : 1_i;
        inference.infer(logger, n_values >= max(distinct_floor, Integer(all_definite_values.size())), JustifyUsingRUP{hints::NValue{owner}}, generic_reason(state, all_vars));

        return PropagatorState::Enable; }, triggers);
}

auto NValue::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    std::vector<SExpr> vars;
    for (const auto & var : _vars)
        vars.push_back(tracker.s_expr_term_of(var));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("nvalue"),
        SExpr::list(std::move(vars)),
        tracker.s_expr_term_of(_n_values)});
}
