#include <gcs/constraints/global_cardinality.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/lp_justifier.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
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
    shared_ptr<LPJustifier> lp_justifier;

    if (optional_model) {
        lp_justifier = make_shared<LPJustifier>(LPJustificationOptions{});
        lp_justifier->initialise_with_vars(initial_state, _vars, _counts);

        // Global cardinality encoding
        for (unsigned i = 0; i < _vals->size(); i++) {
            auto var_sum = WeightedPseudoBooleanSum{};
            for (const auto & var : _vars) {
                var_sum += 1_i * (var == _vals->at(i));
            }

            auto geq_con = var_sum + -1_i * _counts[i] >= 0_i;
            auto leq_con = var_sum + -1_i * _counts[i] <= 0_i;
            auto line1 = optional_model->add_constraint("GlobalCardinality", "vals geq count", geq_con);
            lp_justifier->add_pb_constraint(geq_con, *line1);
            auto line2 = optional_model->add_constraint("GlobalCardinality", "vals leq count", leq_con);
            lp_justifier->add_pb_constraint(leq_con, *line2);
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
            lp_justifier = move(lp_justifier)](const State & state, auto & inference,
            ProofLogger * const logger) -> PropagatorState {
            // Probably very bad: attempt to get domain-consistency using the lp justifier
            // Ideally replace this with a flow propagator
            for (const auto & var : vars) {
                state.for_each_value(var, [&](Integer val) {
                    auto [lower, lower_just, upper, upper_just] = lp_justifier->compute_bounds_and_justifications(state, *logger, var == val);
                    if (lower > 0_i) {
                        inference.infer(logger, var == val, JustifyExplicitlyOnly{lower_just}, {});
                    }
                    else if (upper < 1_i) {
                        inference.infer(logger, var != val, JustifyExplicitlyOnly{upper_just}, {});
                    }
                });
            }

            // Maybe slightly less dumb to use the LP justifier to get bounds-consistency on the counts
            for (const auto & count : counts) {
                auto [lower, lower_just, upper, upper_just] = lp_justifier->compute_bounds_and_justifications(state, *logger, count);
                inference.infer(logger, count >= lower, JustifyExplicitlyOnly{lower_just}, {});
                inference.infer(logger, count < upper - 1_i, JustifyExplicitlyOnly{upper_just}, {});
            }
            return PropagatorState::Enable;
        },
        triggers, "gcc");
}
