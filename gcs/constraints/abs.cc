#include <gcs/constraints/abs.hh>
#include <gcs/constraints/abs/justify.hh>
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

    // _v2 = abs(_v1)
    Triggers triggers{.on_change = {_v1, _v2}};
    propagators.install([v1 = _v1, v2 = _v2](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        // remove from v1 any value whose absolute value isn't in v2's domain.
        for (const auto & val : state.each_value_mutable(v1))
            if (! state.in_domain(v2, abs(val))) {
                inference.infer_not_equal(logger, v1, val, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{v2 != abs(val)}; }});
            }

        // now remove from v2 any value whose +/-value isn't in v1's domain.
        for (const auto & val : state.each_value_mutable(v2)) {
            if (! state.in_domain(v1, val) && ! state.in_domain(v1, -val) && state.in_domain(v2, val)) {
                auto just = [v1, v2, val, logger](const ReasonFunction & reason) {
                    justify_abs_hole(*logger, reason, v1, v2, val);
                };
                inference.infer_not_equal(logger, v2, val, JustifyExplicitly{just}, ReasonFunction{[=]() { return Reason{{v1 != val, v1 != -val}}; }});
            }
        }

        return PropagatorState::Enable;
    },
        triggers, "abs");

    if (optional_model) {
        optional_model->add_constraint("Abs", "non-negative", WPBSum{} + 1_i * _v2 + -1_i * _v1 == 0_i, Reason{_v1 >= 0_i});
        optional_model->add_constraint("Abs", "negative", WPBSum{} + 1_i * _v2 + 1_i * _v1 == 0_i, Reason{_v1 < 0_i});
    }
}
