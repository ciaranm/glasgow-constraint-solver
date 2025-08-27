#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <algorithm>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::pair;
using std::string;
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

auto ArrayMinMax::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (_vars.empty())
        throw UnexpectedException{"not sure how min and max are defined over an empty array"};

    Triggers triggers{.on_change = {_result}};
    for (const auto & v : _vars)
        triggers.on_change.emplace_back(v);

    propagators.install([vars = _vars, result = _result, min = _min](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        // result <= upper bound of each vars
        for (auto & var : vars) {
            auto var_bounds = state.bounds(var);
            if (min)
                inference.infer_less_than(logger, result, var_bounds.second + 1_i, JustifyUsingRUP{}, Reason{[=]() { return Literals{{var < var_bounds.second + 1_i}}; }});
            else
                inference.infer_greater_than_or_equal(logger, result, var_bounds.first, JustifyUsingRUP{}, Reason{[=]() { return Literals{{var >= var_bounds.first}}; }});
        }

        // each var >= result
        auto result_bounds = state.bounds(result);
        for (auto & var : vars) {
            if (min)
                inference.infer_greater_than_or_equal(logger, var, result_bounds.first, JustifyUsingRUP{}, Reason{[=]() { return Literals{{result >= result_bounds.first}}; }});
            else
                inference.infer_less_than(logger, var, state.upper_bound(result) + 1_i, JustifyUsingRUP{}, Reason{[=]() { return Literals{{result < result_bounds.second + 1_i}}; }});
        }

        // result in union(vars)
        for (auto value : state.each_value_mutable(result)) {
            bool found_support = false;
            for (auto & var : vars) {
                if (state.in_domain(var, value)) {
                    found_support = true;
                    break;
                }
            }

            if (! found_support) {
                Literals reason;
                for (auto & var : vars)
                    reason.emplace_back(var != value);
                inference.infer_not_equal(logger, result, value, JustifyUsingRUP{}, Reason{[=]() { return reason; }});
            }
        }

        // is there more than one variable that can support the values in result?
        optional<IntegerVariableID> support_1, support_2;
        for (auto & var : vars) {
            if (any_of(state.each_value_immutable(result), [&](const Integer & val) { return state.in_domain(var, val); })) {
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
            Literals reason = generic_reason(state, vector{result})();

            for (auto & var : vars) {
                if (var == *support_1)
                    continue;
                for (const auto & val : state.each_value_immutable(result))
                    reason.emplace_back(var != val);
            }

            for (const auto & val : state.each_value_mutable(*support_1))
                if (! state.in_domain(result, val))
                    inference.infer(logger, *support_1 != val, JustifyUsingRUP{}, Reason{[=]() { return reason; }});
        }

        return PropagatorState::Enable;
    },
        triggers, "array min max");

    if (optional_model) {
        // result <= each var
        for (const auto & v : _vars) {
            optional_model->add_constraint("ArrayMinMax", "result compared to value", WeightedPseudoBooleanSum{} + (_min ? -1_i : 1_i) * v + (_min ? 1_i : -1_i) * _result <= 0_i, nullopt);
        }

        // result == i->i in vars
        //        for (auto val : initial_state.each_value_immutable(_result)) {
        //            Literals lits{{_result != val}};
        //            for (auto & v : _vars)
        //                if (initial_state.in_domain(v, val))
        //                    lits.emplace_back(v == val);
        //            optional_model->add_constraint("ArrayMinMax", "result is in vars", move(lits));
        //        }

        auto al1 = WeightedPseudoBooleanSum{};
        for (auto & v : _vars) {
            auto t = optional_model->create_proof_flag("arr_min_max_disj");
            optional_model->add_constraint("ArrayMinMax", "result == val", WeightedPseudoBooleanSum{} + (_min ? 1_i : -1_i) * v + (_min ? -1_i : 1_i) * _result <= 0_i, HalfReifyOnConjunctionOf{t});
            optional_model->add_constraint("ArrayMinMax", "result == val", WeightedPseudoBooleanSum{} + (_min ? 1_i : -1_i) * v + (_min ? -1_i : 1_i) * _result >= 1_i, HalfReifyOnConjunctionOf{! t});
            al1 += 1_i * t;
        }
        optional_model->add_constraint("ArrayMinMax", "result is in vars", move(al1) >= 1_i, nullopt);
    }
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
