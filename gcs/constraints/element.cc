/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/element.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/state.hh>
#include <gcs/low_level_constraint_store.hh>
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

auto Element::convert_to_low_level(LowLevelConstraintStore & constraints, const State & initial_state) && -> void
{
    if (_vars.empty()) {
        constraints.cnf( { } );
        return;
    }

    // _idx_var >= 0, _idx_var < _vars.size()
    constraints.cnf({ _idx_var >= 0_i });
    constraints.cnf({ _idx_var < Integer(_vars.size()) });

    // _var <= max(upper(_vars)), _var >= min(lower(_vars))
    // ...and this should really be just over _vars that _idx_var might cover
    auto max_upper = initial_state.upper_bound(*max_element(_vars.begin(), _vars.end(), [&] (const IntegerVariableID & v, const IntegerVariableID & w) {
                return initial_state.upper_bound(v) < initial_state.upper_bound(w);
                }));
    auto min_lower = initial_state.lower_bound(*min_element(_vars.begin(), _vars.end(), [&] (const IntegerVariableID & v, const IntegerVariableID & w) {
                return initial_state.lower_bound(v) < initial_state.lower_bound(w);
                }));
    constraints.cnf({ _var < max_upper + 1_i });
    constraints.cnf({ _var >= min_lower });

    for_each_with_index(_vars, [&] (auto & v, auto idx) {
        // _idx_var == i -> _var == _vars[idx]
        ComparisonReif{ _var, v, _idx_var == Integer(idx), false, ComparisonOperator::Equals }.convert_to_low_level(constraints, initial_state);
    });
}

auto Element::describe_for_proof() -> std::string
{
    return "arithmetic";
}

