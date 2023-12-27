#include <gcs/constraints/not_equals.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators.hh>

#include <util/overloaded.hh>

#include <algorithm>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::max;
using std::min;
using std::nullopt;
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;

NotEquals::NotEquals(const IntegerVariableID v1, const IntegerVariableID v2) :
    _v1(v1),
    _v2(v2)
{
}

auto NotEquals::clone() const -> unique_ptr<Constraint>
{
    return make_unique<NotEquals>(_v1, _v2);
}

auto NotEquals::install(Propagators & propagators, State & initial_state) && -> void
{
    auto v1_is_constant = initial_state.optional_single_value(_v1);
    auto v2_is_constant = initial_state.optional_single_value(_v2);

    bool convert_to_values_ne = false;

    if (v1_is_constant && v2_is_constant) {
        if (*v1_is_constant == *v2_is_constant) {
            propagators.model_contradiction("NotEquals constraint on two variables with the same constant values");
            return;
        }
    }
    else if (v1_is_constant) {
        propagators.install([v1_is_constant = v1_is_constant, v2 = _v2](State & state) -> pair<Inference, PropagatorState> {
            return pair{state.infer_not_equal(v2, *v1_is_constant, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "not equals");
    }
    else if (v2_is_constant) {
        propagators.install([v2_is_constant = v2_is_constant, v1 = _v1](State & state) -> pair<Inference, PropagatorState> {
            return pair{state.infer_not_equal(v1, *v2_is_constant, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "not equals");
    }
    else {
        if (initial_state.domain_size(_v1) < 100_i && initial_state.domain_size(_v2) < 100_i)
            convert_to_values_ne = true;

        Triggers triggers;
        triggers.on_instantiated = {_v1, _v2};

        visit([&](auto & _v1, auto & _v2) {
            propagators.install([v1 = _v1, v2 = _v2, convert_to_values_ne = convert_to_values_ne](State & state) -> pair<Inference, PropagatorState> {
                auto value1 = state.optional_single_value(v1);
                if (value1)
                    return pair{state.infer_not_equal(v2, *value1, convert_to_values_ne ? Justification{NoJustificationNeeded{}} : Justification{JustifyUsingRUP{}}),
                        PropagatorState::DisableUntilBacktrack};
                auto value2 = state.optional_single_value(v2);
                if (value2)
                    return pair{state.infer_not_equal(v1, *value2, convert_to_values_ne ? Justification{NoJustificationNeeded{}} : Justification{JustifyUsingRUP{}}),
                        PropagatorState::DisableUntilBacktrack};
                return pair{Inference::NoChange, PropagatorState::Enable};
            },
                triggers, "not equals");
        },
            _v1, _v2);

        if (convert_to_values_ne && propagators.want_definitions()) {
            propagators.install([v1 = _v1, v2 = _v2](State & state) -> pair<Inference, PropagatorState> {
                state.infer_true(JustifyExplicitly{[&](Proof & proof) -> void {
                    proof.emit_proof_comment("converting not equals to value encoding");
                    state.for_each_value(v1, [&](Integer val1) {
                        if (state.in_domain(v2, val1)) {
                            proof.emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (v1 != val1) + 1_i * (v2 != val1) >= 1_i, ProofLevel::Top);
                        }
                    });
                }});
                return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
            },
                Triggers{}, "not equals conversion");
        }
    }

    if (propagators.want_definitions()) {
        auto selector = propagators.create_proof_flag("notequals");
        propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * _v1 + -1_i * _v2 <= -1_i,
            HalfReifyOnConjunctionOf{{selector}});
        propagators.define(initial_state, WeightedPseudoBooleanSum{} + -1_i * _v1 + 1_i * _v2 <= -1_i,
            HalfReifyOnConjunctionOf{{! selector}});
    }
}

auto NotEquals::describe_for_proof() -> string
{
    return "not equals";
}
