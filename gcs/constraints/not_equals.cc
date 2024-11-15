#include <gcs/constraints/not_equals.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <util/overloaded.hh>

#include <algorithm>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
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

auto NotEquals::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto v1_is_constant = initial_state.optional_single_value(_v1);
    auto v2_is_constant = initial_state.optional_single_value(_v2);

    bool convert_to_values_ne = false;

    if (v1_is_constant && v2_is_constant) {
        if (*v1_is_constant == *v2_is_constant) {
            propagators.model_contradiction(initial_state, optional_model, "NotEquals constraint on two variables with the same constant values");
            return;
        }
    }
    else if (v1_is_constant) {
        propagators.install_initialiser([v1_is_constant = v1_is_constant, v1 = _v1, v2 = _v2](
                                            const State &, auto & inference, ProofLogger * const logger) -> void {
            inference.infer_not_equal(logger, v2, *v1_is_constant, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 == *v1_is_constant}}; }});
        });
    }
    else if (v2_is_constant) {
        propagators.install_initialiser([v2_is_constant = v2_is_constant, v1 = _v1, v2 = _v2](
                                            const State &, auto & inference, ProofLogger * const logger) -> void {
            inference.infer_not_equal(logger, v1, *v2_is_constant, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v2 == *v2_is_constant}}; }});
        });
    }
    else {
        if (initial_state.domain_size(_v1) < 100_i && initial_state.domain_size(_v2) < 100_i)
            convert_to_values_ne = true;

        Triggers triggers;
        triggers.on_instantiated = {_v1, _v2};

        visit([&](auto & _v1, auto & _v2) {
            propagators.install([v1 = _v1, v2 = _v2, convert_to_values_ne = convert_to_values_ne](
                                    const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                auto value1 = state.optional_single_value(v1);
                if (value1) {
                    if (convert_to_values_ne) {
                        inference.infer_not_equal(logger, v2, *value1, NoJustificationNeeded{}, Reason{});
                        return PropagatorState::DisableUntilBacktrack;
                    }
                    else {
                        inference.infer_not_equal(logger, v2, *value1,
                            JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 == *value1}}; }});
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
                auto value2 = state.optional_single_value(v2);
                if (value2) {
                    if (convert_to_values_ne) {
                        inference.infer_not_equal(logger, v1, *value2, NoJustificationNeeded{}, Reason{});
                        return PropagatorState::DisableUntilBacktrack;
                    }
                    else {
                        inference.infer_not_equal(logger, v1, *value2, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v2 == *value2}}; }});
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
                return PropagatorState::Enable;
            },
                triggers, "not equals");
        },
            _v1, _v2);

        if (convert_to_values_ne && optional_model) {
            propagators.install_initialiser([v1 = _v1, v2 = _v2](
                                                const State & state, auto &, ProofLogger * const logger) -> void {
                logger->emit_proof_comment("converting not equals to value encoding");
                for (auto val1 : state.each_value_immutable(v1))
                    if (state.in_domain(v2, val1)) {
                        logger->emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (v1 != val1) + 1_i * (v2 != val1) >= 1_i, ProofLevel::Top);
                    }
            });
        }
    }

    if (optional_model) {
        auto selector = optional_model->create_proof_flag("notequals");
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * _v1 + -1_i * _v2 <= -1_i,
            HalfReifyOnConjunctionOf{{selector}});
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + -1_i * _v1 + 1_i * _v2 <= -1_i,
            HalfReifyOnConjunctionOf{{! selector}});
    }
}

auto NotEquals::describe_for_proof() -> string
{
    return "not equals";
}
