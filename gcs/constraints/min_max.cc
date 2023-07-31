#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/exception.hh>
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

auto ArrayMinMax::install(Propagators & propagators, State & initial_state) && -> void
{
    if (_vars.empty())
        throw UnexpectedException{"not sure how min and max are defined over an empty array"};

    Triggers triggers{.on_change = {_result}};
    for (const auto & v : _vars)
        triggers.on_change.emplace_back(v);

    propagators.install([vars = _vars, result = _result, min = _min](State & state) -> pair<Inference, PropagatorState> {
        Inference inf = Inference::NoChange;

        // result <= each var
        for (auto & var : vars) {
            if (min)
                increase_inference_to(inf, state.infer_less_than(result, state.upper_bound(var) + 1_i, JustifyUsingRUP{}));
            else
                increase_inference_to(inf, state.infer_greater_than_or_equal(result, state.lower_bound(var), JustifyUsingRUP{}));

            if (Inference::Contradiction == inf)
                return pair{inf, PropagatorState::Enable};
        }

        // each var >= result
        for (auto & var : vars) {
            if (min)
                increase_inference_to(inf, state.infer_greater_than_or_equal(var, state.lower_bound(result), JustifyUsingRUP{}));
            else
                increase_inference_to(inf, state.infer_less_than(result, state.upper_bound(result) + 1_i, JustifyUsingRUP{}));

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
                increase_inference_to(inf, state.infer_not_equal(result, value, JustifyUsingRUP{}));
                if (Inference::Contradiction == inf)
                    return false;
            }

            return true;
        });

        if (Inference::Contradiction == inf)
            return pair{inf, PropagatorState::Enable};

        // largest value in result uniquely supported?
        optional<IntegerVariableID> support_of_largest_1, support_of_largest_2;
        auto largest_result = state.upper_bound(result);
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
        else if (! support_of_largest_2)
            increase_inference_to(inf, state.infer_less_than(*support_of_largest_1, largest_result + 1_i, JustifyUsingRUP{}));

        return pair{inf, PropagatorState::Enable};
    },
        triggers, "array min max");

    if (propagators.want_definitions()) {
        // result <= each var
        for (const auto & v : _vars) {
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + (_min ? -1_i : 1_i) * v + (_min ? 1_i : -1_i) * _result <= 0_i, nullopt);
        }

        // result == i -> i in vars
        initial_state.for_each_value(_result, [&](Integer val) {
            Literals lits{{_result != val}};
            for (auto & v : _vars)
                if (initial_state.in_domain(v, val))
                    lits.emplace_back(v == val);
            propagators.define_cnf(initial_state, move(lits));
        });
    }
}

auto ArrayMinMax::describe_for_proof() -> string
{
    return "array min max";
}

Min::Min(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result) :
    ArrayMinMax(_vs, result, true),
    _vs({v1, v2})
{
}

Max::Max(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result) :
    ArrayMinMax(_vs, result, false),
    _vs({v1, v2})
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
