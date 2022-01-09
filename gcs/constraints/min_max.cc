/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/min_max.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/propagators.hh>
#include <gcs/exception.hh>
#include <util/for_each.hh>

using namespace gcs;

ArrayMinMax::ArrayMinMax(const std::vector<IntegerVariableID> & vars, const IntegerVariableID result, bool min) :
    _vars(vars),
    _result(result),
    _min(min)
{
}

auto ArrayMinMax::install(Propagators & propagators, const State & initial_state) && -> void
{
    if (_vars.empty())
        throw UnexpectedException{ "not sure how min and max are defined over an empty array" };

    if (_min) {
        for (auto & v : _vars)
            LessThanEqual{ _result, v }.install(propagators, initial_state);
    }
    else {
        for (auto & v : _vars)
            LessThanEqual{ v, _result }.install(propagators, initial_state);
    }

    auto selector = propagators.create_auxilliary_integer_variable(0_i, Integer(_vars.size() - 1), "minmax");
    for_each_with_index(_vars, [&] (IntegerVariableID var, auto idx) {
            // (selector == idx /\ var == val) -> result == val
            initial_state.for_each_value(var, [&] (Integer val) {
                    propagators.cnf(initial_state, { selector != Integer(idx), var != val, _result == val }, true);
                    });
            // (selector == idx /\ result == r) -> var == r
            initial_state.for_each_value(_result, [&] (Integer r) {
                    propagators.cnf(initial_state, { selector != Integer(idx), _result != r, var == r }, true);
                    });
    });

    // selector isn't branched on, so need to force it to be the lowest possible thing it can be
    // in case two variables have the same min or max value
    for_each_with_index(_vars, [&] (IntegerVariableID v1, auto v1_idx) {
            for_each_with_index(_vars, [&] (IntegerVariableID v2, auto v2_idx) {
                    if (v1_idx < v2_idx) {
                        // v1 == v2 -> selector != v2
                        initial_state.for_each_value(v1, [&] (Integer val) {
                                if (initial_state.in_domain(v2, val)) {
                                    propagators.cnf(initial_state, { v1 != val, v2 != val, selector != Integer(v2_idx) }, true);
                                }
                            });
                    }
                });
            });
}

auto ArrayMinMax::describe_for_proof() -> std::string
{
    return "array min max";
}

Min::Min(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result) :
    ArrayMinMax(_vs, result, true),
    _vs({ v1, v2 })
{
}

Max::Max(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result) :
    ArrayMinMax(_vs, result, false),
    _vs({ v1, v2 })
{
}

ArrayMin::ArrayMin(const std::vector<IntegerVariableID> & vars, const IntegerVariableID result) :
    ArrayMinMax(vars, result, true)
{
}

ArrayMax::ArrayMax(const std::vector<IntegerVariableID> & vars, const IntegerVariableID result) :
    ArrayMinMax(vars, result, false)
{
}

