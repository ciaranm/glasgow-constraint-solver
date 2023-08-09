#include <gcs/constraints/abs.hh>
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

auto Abs::install(Propagators & propagators, State & initial_state) && -> void
{
    // _v2 >= 0
    propagators.trim_lower_bound(initial_state, _v2, 0_i, "Abs");

    // _v1 <= upper_bound(_v2)
    propagators.trim_upper_bound(initial_state, _v1, initial_state.upper_bound(_v2), "Abs");

    // _v1 >= -upper_bound(_v2)
    propagators.trim_lower_bound(initial_state, _v1, -initial_state.upper_bound(_v2), "Abs");

    // _v2 <= max(upper_bound(_v1), -lower_bound(_v1))
    auto v2u = max(initial_state.upper_bound(_v1), -initial_state.lower_bound(_v1));
    propagators.trim_upper_bound(initial_state, _v2, v2u, "Abs");

    optional<ProofFlag> selector;
    if (propagators.want_definitions())
        selector = propagators.create_proof_flag("abs");

    // _v2 = abs(_v1)
    Triggers triggers{.on_change = {_v1, _v2}};
    propagators.install([v1 = _v1, v2 = _v2, selector = selector](State & state) -> pair<Inference, PropagatorState> {
        // v2 = abs(v1)
        Inference result = Inference::NoChange;
        state.for_each_value_while(v1, [&](Integer val) {
            if (! state.in_domain(v2, abs(val)))
                increase_inference_to(result, state.infer_not_equal(v1, val, JustifyUsingRUP{}));
            return result != Inference::Contradiction;
        });

        state.for_each_value_while(v2, [&](Integer val) {
            if (! state.in_domain(v1, val) && ! state.in_domain(v1, -val) && state.in_domain(v2, val))
                increase_inference_to(result, state.infer_not_equal(v2, val, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & del) {
                    del.push_back(proof.emit_rup_proof_line_under_trail(state,
                        WeightedPseudoBooleanSum{} + 1_i * (v1 != val) >= 1_i));
                    del.push_back(proof.emit_rup_proof_line_under_trail(state,
                        WeightedPseudoBooleanSum{} + 1_i * (v1 != -val) >= 1_i));
                    del.push_back(proof.emit_rup_proof_line_under_trail(state,
                        WeightedPseudoBooleanSum{} + 1_i * (*selector) + 1_i * (v2 != val) >= 1_i));
                    del.push_back(proof.emit_rup_proof_line_under_trail(state,
                        WeightedPseudoBooleanSum{} + 1_i * (! *selector) + 1_i * (v2 != val) >= 1_i));
                }}));
            return result != Inference::Contradiction;
        });

        return pair{result, PropagatorState::Enable};
    },
        triggers, "abs");

    if (propagators.want_definitions()) {
        propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * _v2 + -1_i * _v1 == 0_i, HalfReifyOnConjunctionOf{*selector});
        propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * _v1 + 1_i * _v2 == 0_i, HalfReifyOnConjunctionOf{! *selector});
        propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * _v1 <= -1_i, HalfReifyOnConjunctionOf{! *selector});
        propagators.define(initial_state, WeightedPseudoBooleanSum{} + -1_i * _v1 <= 0_i, HalfReifyOnConjunctionOf{*selector});
    }
}

auto Abs::describe_for_proof() -> std::string
{
    return "abs";
}
