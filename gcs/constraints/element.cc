/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/element.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/state.hh>
#include <gcs/propagators.hh>
#include <gcs/integer.hh>

#include <util/for_each.hh>

#include <algorithm>

using namespace gcs;

using std::max;
using std::min;
using std::vector;

Element::Element(IntegerVariableID var, IntegerVariableID idx_var, const vector<IntegerVariableID> & vars) :
    _var(var),
    _idx_var(idx_var),
    _vars(vars)
{
}

auto Element::install(Propagators & propagators, const State & initial_state) && -> void
{
    if (_vars.empty()) {
        propagators.cnf(initial_state, { }, true);
        return;
    }

    // _idx_var >= 0, _idx_var < _vars.size()
    propagators.trim_lower_bound(initial_state, _idx_var, 0_i);
    propagators.trim_upper_bound(initial_state, _idx_var, Integer(_vars.size()) - 1_i);

    // _var <= max(upper(_vars)), _var >= min(lower(_vars))
    // ...and this should really be just over _vars that _idx_var might cover
    auto max_upper = initial_state.upper_bound(*max_element(_vars.begin(), _vars.end(), [&] (const IntegerVariableID & v, const IntegerVariableID & w) {
                return initial_state.upper_bound(v) < initial_state.upper_bound(w);
                }));
    auto min_lower = initial_state.lower_bound(*min_element(_vars.begin(), _vars.end(), [&] (const IntegerVariableID & v, const IntegerVariableID & w) {
                return initial_state.lower_bound(v) < initial_state.lower_bound(w);
                }));

    propagators.trim_lower_bound(initial_state, _var, min_lower);
    propagators.trim_upper_bound(initial_state, _var, max_upper);

    for_each_with_index(_vars, [&] (auto & v, auto idx) {
        // _idx_var == i -> _var == _vars[idx]
        if (initial_state.in_domain(_idx_var, Integer(idx)))
            EqualsIf{ _var, v, _idx_var == Integer(idx) }.install(propagators, initial_state);
    });

    initial_state.for_each_value(_var, [&] (Integer val) {
            // _var == val -> exists i . _vars[idx] == val
            Literals options;
            options.emplace_back(_var != val);
            for_each_with_index(_vars, [&] (auto & v, auto idx) {
                    if (initial_state.in_domain(_idx_var, Integer(idx)) && initial_state.in_domain(v, val))
                        options.emplace_back(v == val);
            });
            propagators.cnf(initial_state, move(options), true);
    });
}

auto Element::describe_for_proof() -> std::string
{
    return "element";
}

