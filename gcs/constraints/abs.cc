#include <gcs/constraints/abs.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <optional>

using namespace gcs;
using namespace gcs::innards;

using std::max;
using std::optional;
using std::pair;
using std::unique_ptr;
using std::vector;

Abs::Abs(const IntegerVariableID v1, const IntegerVariableID v2) :
    _v1(v1),
    _v2(v2)
{
}

auto Abs::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Abs>(_v1, _v2);
}

auto Abs::install(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) && -> void
{
    // _v2 >= 0
    propagators.trim_lower_bound(initial_state, optional_model, _v2, 0_i, "Abs");

    // _v1 <= upper_bound(_v2)
    propagators.trim_upper_bound(initial_state, optional_model, _v1, initial_state.upper_bound(_v2), "Abs");

    // _v1 >= -upper_bound(_v2)
    propagators.trim_lower_bound(initial_state, optional_model, _v1, -initial_state.upper_bound(_v2), "Abs");

    // _v2 <= max(upper_bound(_v1), -lower_bound(_v1))
    auto v2u = max(initial_state.upper_bound(_v1), -initial_state.lower_bound(_v1));
    propagators.trim_upper_bound(initial_state, optional_model, _v2, v2u, "Abs");

    optional<ProofFlag> selector;
    if (optional_model)
        selector = optional_model->create_proof_flag("abs");

    // _v2 = abs(_v1)
    Triggers triggers{.on_change = {_v1, _v2}};
    propagators.install([v1 = _v1, v2 = _v2, selector = selector](
                            const State & state, auto & inference) -> PropagatorState {
        // we're not dealing with bounds. remove from v1 any value whose absolute value
        // isn't in v2's domain.
        state.for_each_value(v1, [&](Integer val) {
            if (! state.in_domain(v2, abs(val)))
                inference.infer_not_equal(v1, val, JustifyUsingRUP{}, Reason{[=]() { return Literals{v2 != abs(val)}; }});
        });

        // now remove from v2 any value whose +/-value isn't in v1's domain.
        state.for_each_value(v2, [&](Integer val) {
            if (! state.in_domain(v1, val) && ! state.in_domain(v1, -val) && state.in_domain(v2, val)) {
                auto just = [selector, v1, v2, val](const Reason & reason, ProofLogger & logger) {
                    logger.emit_rup_proof_line_under_reason(reason,
                        WeightedPseudoBooleanSum{} + 1_i * (*selector) + 1_i * (v2 != val) >= 1_i, ProofLevel::Temporary);
                    logger.emit_rup_proof_line_under_reason(reason,
                        WeightedPseudoBooleanSum{} + 1_i * (! *selector) + 1_i * (v2 != val) >= 1_i, ProofLevel::Temporary);
                };
                inference.infer_not_equal(v2, val, JustifyExplicitly{just}, Reason{[=]() { return Literals{{v1 != val, v1 != -val}}; }});
            }
        });

        return PropagatorState::Enable;
    },
        triggers, "abs");

    if (optional_model) {
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * _v2 + -1_i * _v1 == 0_i, HalfReifyOnConjunctionOf{*selector});
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * _v1 + 1_i * _v2 == 0_i, HalfReifyOnConjunctionOf{! *selector});
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * _v1 <= -1_i, HalfReifyOnConjunctionOf{! *selector});
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + -1_i * _v1 <= 0_i, HalfReifyOnConjunctionOf{*selector});
    }
}

auto Abs::describe_for_proof() -> std::string
{
    return "abs";
}
