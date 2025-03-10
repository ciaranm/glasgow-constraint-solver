#include <gcs/constraints/global_cardinality.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/lp_justifier.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::make_unique;
using std::shared_ptr;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

GlobalCardinalityBC::GlobalCardinalityBC(vector<IntegerVariableID> vars,
    std::vector<Integer> * vals,
    std::vector<IntegerVariableID> counts) :
    _vars(vars),
    _vals(move(vals)),
    _counts(counts)
{
}

auto GlobalCardinalityBC::clone() const -> unique_ptr<Constraint>
{
    return make_unique<GlobalCardinalityBC>(_vars, _vals, _counts);
}

auto GlobalCardinalityBC::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    unique_ptr<LPJustifier> lp_justifier;
    lp_justifier = make_unique<LPJustifier>(LPJustificationOptions{});
    lp_justifier->initialise_with_vars(initial_state, _vars, _counts);
    // Global cardinality encoding
    for (unsigned i = 0; i < _vals->size(); i++) {
        auto var_sum = WeightedPseudoBooleanSum{};
        for (const auto & var : _vars) {
            var_sum += 1_i * (var == _vals->at(i));
        }

        auto geq_con = var_sum + -1_i * _counts[i] >= 0_i;
        auto leq_con = var_sum + -1_i * _counts[i] <= 0_i;

        if (optional_model) {
            auto line1 = optional_model->add_constraint("GlobalCardinality", "vals geq count", geq_con);
            lp_justifier->add_pb_constraint(geq_con, *line1);
            auto line2 = optional_model->add_constraint("GlobalCardinality", "vals leq count", leq_con);
            lp_justifier->add_pb_constraint(leq_con, *line2);
        }
        else {
            lp_justifier->add_pb_constraint(geq_con, 0);
            lp_justifier->add_pb_constraint(leq_con, 0);
        }
    }

    Triggers triggers{};
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_change.insert(triggers.on_change.end(), _counts.begin(), _counts.end());

    vector<Integer> compressed_vals;

    for (auto & var : _vars)
        for (const auto & val : initial_state.each_value_immutable(var))
            if (compressed_vals.end() == find(compressed_vals.begin(), compressed_vals.end(), val))
                compressed_vals.push_back(val);

    propagators.install(
        [vars = move(_vars),
            vals = move(compressed_vals),
            counts = move(_counts),
            lp_justifier_ptr = move(lp_justifier)](const State & state, auto & inference,
            ProofLogger * const logger) -> PropagatorState {
            LPJustifier * lp_justifier = lp_justifier_ptr.get();
            // Probably very bad: attempt to get domain-consistency using the lp justifier
            // Ideally replace this with a flow propagator
            for (const auto & var : vars) {
                auto contr = false;
                if (state.has_single_value(var))
                    continue;

                state.for_each_value_while(var, [&](Integer val) {
                    auto [lower, lower_just] = lp_justifier->compute_bound_and_justifications(state, *logger,
                        WeightedPseudoBooleanSum{} + -1_i * (var == val));
                    lower = -lower;

                    if (lower > 1_i) {
                        // Ugh
                        logger->emit_proof_comment("Inferred Contradiction!");
                        auto just = lp_justifier->compute_justification(state, *logger, WeightedPseudoBooleanSum{} >= 1_i);
                        inference.infer(logger, FalseLiteral{}, JustifyExplicitlyOnly{just}, {});
                        contr = true;
                        return false;
                    }
                    else if (lower > 0_i) {

                        inference.infer(logger, var == val, JustifyExplicitlyOnly{lower_just}, {});
                    }

                    auto [upper, upper_just] = lp_justifier->compute_bound_and_justifications(state, *logger,
                        WeightedPseudoBooleanSum{} + 1_i * (var == val));

                    if (upper < 1_i) {
                        inference.infer(logger, var != val, JustifyExplicitlyOnly{upper_just}, {});
                        if (state.has_single_value(var)) {
                            // Inferred contradiction
                            contr = true;
                            return false;
                        }
                    }
                    return true;
                });

                if (contr) {
                    return PropagatorState::Enable;
                }
            }

            // Maybe slightly less dumb to use the LP justifier to get bounds-consistency on the counts
            for (const auto & count : counts) {
                if (state.has_single_value(count))
                    continue;
                auto [prev_lower, prev_upper] = state.bounds(count);
                auto [lower, lower_just] = lp_justifier->compute_bound_and_justifications(state, *logger,
                    WeightedPseudoBooleanSum{} + -1_i * count);
                lower = -lower;
                inference.infer(logger, count >= lower, JustifyExplicitlyOnly{lower_just}, {});
                if (lower > prev_upper)
                    return PropagatorState::Enable;

                auto [upper, upper_just] = lp_justifier->compute_bound_and_justifications(state, *logger,
                    WeightedPseudoBooleanSum{} + 1_i * count);

                inference.infer(logger, count < upper + 1_i, JustifyExplicitlyOnly{upper_just}, {});
                if (lower > upper)
                    return PropagatorState::Enable;
            }
            return PropagatorState::Enable;
        },
        triggers, "gcc");
}
