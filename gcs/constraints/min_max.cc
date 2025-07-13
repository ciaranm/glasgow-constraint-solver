#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;
using std::ranges::any_of;

ArrayMinMax::ArrayMinMax(vector<IntegerVariableID> vars, const IntegerVariableID result, bool min) :
    _vars(move(vars)),
    _result(result),
    _min(min)
{
}

auto ArrayMinMax::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ArrayMinMax>(_vars, _result, _min);
}

auto ArrayMinMax::install(Propagators & propagators, State &, ProofModel * const optional_model) && -> void
{
    if (_vars.empty())
        throw UnexpectedException{"not sure how min and max are defined over an empty array"};

    Triggers triggers{.on_change = {_result}};
    for (const auto & v : _vars)
        triggers.on_change.emplace_back(v);

    vector<ProofFlag> selectors;
    if (optional_model) {
        // (for min) each var >= result, i.e. var - result >= 0
        for (const auto & v : _vars) {
            optional_model->add_constraint("ArrayMinMax", "result compared to value", WeightedPseudoBooleanSum{} + (_min ? 1_i : -1_i) * v + (_min ? -1_i : 1_i) * _result >= 0_i, nullopt);
        }

        WeightedPseudoBooleanSum al1_selector;

        // (for min) f_i <-> var[i] <= result, i.e. var - result <= 0
        for (const auto & [id, var] : enumerate(_vars)) {
            auto selector = optional_model->create_proof_flag("arrayminmax" + to_string(id));
            selectors.push_back(selector);
            optional_model->add_constraint("ArrayMinMax", "result is this value", WeightedPseudoBooleanSum{} + (_min ? 1_i : -1_i) * var + (_min ? -1_i : 1_i) * _result <= 0_i, {{selector}});
            optional_model->add_constraint("ArrayMinMax", "result is this value", WeightedPseudoBooleanSum{} + (_min ? 1_i : -1_i) * var + (_min ? -1_i : 1_i) * _result >= 1_i, {{! selector}});
            al1_selector += 1_i * selector;
        }

        // sum f_i >= 1
        optional_model->add_constraint("ArrayMinMax", "result is one of the values", al1_selector >= 1_i);
    }

    propagators.install([vars = _vars, result = _result, min = _min, selectors = selectors](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        // result <= upper bound of each vars
        for (auto & var : vars) {
            auto var_bounds = state.bounds(var);
            if (min)
                inference.infer_less_than(logger, result, var_bounds.second + 1_i, JustifyUsingRUP{}, ExpandedReason{{var < var_bounds.second + 1_i}});
            else
                inference.infer_greater_than_or_equal(logger, result, var_bounds.first, JustifyUsingRUP{}, ExpandedReason{{var >= var_bounds.first}});
        }

        // each var >= result
        auto result_bounds = state.bounds(result);
        for (auto & var : vars) {
            if (min)
                inference.infer_greater_than_or_equal(logger, var, result_bounds.first, JustifyUsingRUP{}, ExpandedReason{{result >= result_bounds.first}});
            else
                inference.infer_less_than(logger, var, state.upper_bound(result) + 1_i, JustifyUsingRUP{}, ExpandedReason{{result < result_bounds.second + 1_i}});
        }

        // result in union(vars)
        for (auto value : state.each_value(result)) {
            bool found_support = false;
            for (auto & var : vars) {
                if (state.in_domain(var, value)) {
                    found_support = true;
                    break;
                }
            }

            if (! found_support) {
                ExpandedReason reason;
                for (auto & var : vars)
                    reason.emplace_back(var != value);

                inference.infer_not_equal(logger, result, value, JustifyExplicitly{[result, value, &selectors](ProofLogger & logger, const ExpandedReason & reason) {
                    // show that none of the selectors work, if we're taking the result to be that value and also
                    // that the value is missing from all of the vars
                    for (const auto & sel : selectors)
                        logger.emit_rup_proof_line_under_reason(reason, WeightedPseudoBooleanSum{} + (1_i * ! sel) + (1_i * (result != value)) >= 1_i, ProofLevel::Temporary);
                }},
                    reason);
            }
        }

        // is there more than one variable that can support the values in result?
        optional<IntegerVariableID> support_1, support_2;
        for (auto & var : vars) {
            if (any_of(state.each_value(result), [&] (const Integer & val) { return state.in_domain(var, val); })) {
                if (! support_1)
                    support_1 = var;
                else {
                    support_2 = var;
                    break;
                }
            }
        }

        if (! support_1)
            throw UnexpectedException{"missing support, bug in MinMaxArray propagator"};
        else if (! support_2) {
            // no, there's only a single var left that has any intersection with result. so, that
            // variable has to lose any values not present in result.
            DetailedReasonOutline reason;
            reason.emplace_back(ExactValuesLost{result});

            for (auto & var : vars) {
                if (var == *support_1)
                    continue;
                for (const auto & val : state.each_value(result))
                    reason.emplace_back(var != val);
            }

            for (const auto & val : state.each_value(*support_1))
                if (! state.in_domain(result, val)) {
                    auto justf = JustifyExplicitly{[&vars, support_1 = *support_1, result, val, result_values = state.copy_of_values(result), &selectors](
                                                       ProofLogger & logger, const ExpandedReason & reason) {
                        // first, show that the selector can't be true for anything other than the supporting variable
                        for (const auto & [idx, var] : enumerate(vars)) {
                            if (var != support_1) {
                                for (const auto & val : result_values.each())
                                    logger.emit_rup_proof_line_under_reason(reason, WeightedPseudoBooleanSum{} + (1_i * ! selectors.at(idx)) + (1_i * (result != val)) >= 1_i, ProofLevel::Temporary);
                                logger.emit_rup_proof_line_under_reason(reason, WeightedPseudoBooleanSum{} + (1_i * ! selectors.at(idx)) >= 1_i, ProofLevel::Temporary);
                            }
                        }
                        // now fish out the supporting variable, and show that it has to have its selector true
                        for (const auto & [idx, var] : enumerate(vars)) {
                            if (var == support_1)
                                logger.emit_rup_proof_line_under_reason(reason, WeightedPseudoBooleanSum{} + (1_i * (support_1 == val)) + (1_i * selectors.at(idx)) >= 1_i, ProofLevel::Temporary);
                        }
                    }};
                    inference.infer(logger, *support_1 != val, justf, reason);
                }
        }

        return PropagatorState::Enable;
    },
        {_result, _vars}, triggers, "array min max");
}

Min::Min(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result) :
    ArrayMinMax({v1, v2}, result, true)
{
}

Max::Max(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result) :
    ArrayMinMax({v1, v2}, result, false)
{
}

ArrayMin::ArrayMin(vector<IntegerVariableID> vars, const IntegerVariableID result) :
    ArrayMinMax(move(vars), result, true)
{
}

ArrayMax::ArrayMax(vector<IntegerVariableID> vars, const IntegerVariableID result) :
    ArrayMinMax(move(vars), result, false)
{
}
