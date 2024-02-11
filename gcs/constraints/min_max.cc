#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::unique_ptr;
using std::vector;

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

    propagators.install([vars = _vars, result = _result, min = _min](State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
        Inference inf = Inference::NoChange;

        // result <= upper bound of each vars
        for (auto & var : vars) {
            auto var_bounds = state.bounds(var);
            if (min)
                increase_inference_to(inf, state.infer_less_than(logger, result, var_bounds.second + 1_i, JustifyUsingRUPBecauseOf{{var < var_bounds.second + 1_i}}));
            else
                increase_inference_to(inf, state.infer_greater_than_or_equal(logger, result, var_bounds.first, JustifyUsingRUPBecauseOf{{var >= var_bounds.first}}));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};
        }

        // each var >= result
        auto result_bounds = state.bounds(result);
        for (auto & var : vars) {
            if (min)
                increase_inference_to(inf, state.infer_greater_than_or_equal(logger, var, result_bounds.first, JustifyUsingRUPBecauseOf{{result >= result_bounds.first}}));
            else
                increase_inference_to(inf, state.infer_less_than(logger, var, state.upper_bound(result) + 1_i, JustifyUsingRUPBecauseOf{{result < result_bounds.second + 1_i}}));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};
        }

        // result in union(vars)
        state.for_each_value(result, [&](Integer value) {
            bool found_support = false;
            for (auto & var : vars) {
                if (state.in_domain(var, value)) {
                    found_support = true;
                    break;
                }
            }

            if (! found_support) {
                Reason reason;
                for (auto & var : vars)
                    reason.emplace_back(var != value);
                increase_inference_to(inf, state.infer_not_equal(logger, result, value, JustifyUsingRUPBecauseOf{move(reason)}));
                if (Inference::Contradiction == inf)
                    return false;
            }

            return true;
        });

        if (Inference::Contradiction == inf)
            return pair{inf, PropagatorState::Enable};

        // largest value in result uniquely supported?
        optional<IntegerVariableID> support_of_largest_1, support_of_largest_2;
        auto largest_result = min ? state.upper_bound(result) : state.lower_bound(result);
        for (auto & var : vars) {
            if (state.in_domain(var, largest_result)) {
                if (! support_of_largest_1)
                    support_of_largest_1 = var;
                else {
                    support_of_largest_2 = var;
                    break;
                }
            }
        }

        if (! support_of_largest_1)
            throw UnexpectedException{"missing support, bug in MinMaxArray propagator"};
        else if (! support_of_largest_2) {
            Reason reason;
            reason.emplace_back(result == largest_result);

            for (auto & var : vars) {
                if (var == *support_of_largest_1)
                    continue;
                if (! min)
                    reason.emplace_back(var < largest_result);
                else
                    reason.emplace_back(var >= largest_result + 1_i);
            }

            if (min) {
                increase_inference_to(inf, state.infer_less_than(logger, *support_of_largest_1, largest_result + 1_i, JustifyUsingRUPBecauseOf{move(reason)}));
            }
            else {
                increase_inference_to(inf, state.infer_greater_than_or_equal(logger, *support_of_largest_1, largest_result, JustifyUsingRUPBecauseOf{move(reason)}));
            }
        }

        return pair{inf, PropagatorState::Enable};
    },
        triggers, "array min max");

    if (optional_model) {
        // result <= each var
        for (const auto & v : _vars) {
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + (_min ? -1_i : 1_i) * v + (_min ? 1_i : -1_i) * _result <= 0_i, nullopt);
        }

        // result == i -> i in vars
        initial_state.for_each_value(_result, [&](Integer val) {
            Literals lits{{_result != val}};
            for (auto & v : _vars)
                if (initial_state.in_domain(v, val))
                    lits.emplace_back(v == val);
            optional_model->add_constraint(move(lits));
        });
    }
}

auto ArrayMinMax::describe_for_proof() -> string
{
    return "array min max";
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
