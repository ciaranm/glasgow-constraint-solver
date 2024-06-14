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

using std::make_shared;
using std::max;
using std::optional;
using std::pair;
using std::shared_ptr;
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

    shared_ptr<RUPDependencies> rup_dependencies;
    if (optional_model) {
        rup_dependencies = make_shared<RUPDependencies>();
        add_dependency(*rup_dependencies, optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * _v2 + -1_i * _v1 == 0_i, HalfReifyOnConjunctionOf{*selector}));
        add_dependency(*rup_dependencies, optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * _v1 + 1_i * _v2 == 0_i, HalfReifyOnConjunctionOf{! *selector}));
        add_dependency(*rup_dependencies, optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * _v1 <= -1_i, HalfReifyOnConjunctionOf{! *selector}));
        add_dependency(*rup_dependencies, optional_model->add_constraint(WeightedPseudoBooleanSum{} + -1_i * _v1 <= 0_i, HalfReifyOnConjunctionOf{*selector}));
        rup_dependencies->push_back(_v1);
        rup_dependencies->push_back(_v2);
    }

    // _v2 = abs(_v1)
    Triggers triggers{.on_change = {_v1, _v2}};
    propagators.install([v1 = _v1, v2 = _v2, selector = selector, rup_dependencies = rup_dependencies](
                            const State & state, auto & inference) -> PropagatorState {
        // we're not dealing with bounds. remove from v1 any value whose absolute value
        // isn't in v2's domain.
        for (const auto & val : state.each_value_mutable(v1))
            if (! state.in_domain(v2, abs(val)))
                inference.infer_not_equal(v1, val, JustifyUsingRUP{rup_dependencies}, Reason{[=]() { return Literals{v2 != abs(val)}; }});

        // now remove from v2 any value whose +/-value isn't in v1's domain.
        for (const auto & val : state.each_value_mutable(v2)) {
            if (! state.in_domain(v1, val) && ! state.in_domain(v1, -val) && state.in_domain(v2, val)) {
                auto just = [selector, v1, v2, val, rup_dependencies](const Reason & reason, ProofLogger & logger) {
                    logger.emit_rup_proof_line_under_reason(reason,
                        WeightedPseudoBooleanSum{} + 1_i * (*selector) + 1_i * (v2 != val) >= 1_i, ProofLevel::Temporary, rup_dependencies);
                    logger.emit_rup_proof_line_under_reason(reason,
                        WeightedPseudoBooleanSum{} + 1_i * (! *selector) + 1_i * (v2 != val) >= 1_i, ProofLevel::Temporary, rup_dependencies);
                };
                inference.infer_not_equal(v2, val, JustifyExplicitly{just, rup_dependencies}, Reason{[=]() { return Literals{{v1 != val, v1 != -val}}; }});
            }
        }

        return PropagatorState::Enable;
    },
        triggers, "abs");
}

auto Abs::describe_for_proof() -> std::string
{
    return "abs";
}
