/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/abs.hh>
#include <gcs/low_level_constraint_store.hh>
#include <gcs/state.hh>

#include <algorithm>

using namespace gcs;

using std::max;
using std::min;

Abs::Abs(const IntegerVariableID v1, const IntegerVariableID v2) :
    _v1(v1),
    _v2(v2)
{
}

auto Abs::convert_to_low_level(LowLevelConstraintStore & constraints, const State & initial_state) && -> void
{
    // _v2 >= 0
    constraints.trim_lower_bound(initial_state, _v2, 0_i);

    // _v1 <= upper_bound(_v2)
    constraints.trim_upper_bound(initial_state, _v1, initial_state.upper_bound(_v2));

    // _v1 >= -upper_bound(_v2)
    constraints.trim_lower_bound(initial_state, _v1, -initial_state.upper_bound(_v2));

    // _v2 <= max(upper_bound(_v1), -lower_bound(_v1))
    auto v2u = max(initial_state.upper_bound(_v1), -initial_state.lower_bound(_v1));
    constraints.trim_upper_bound(initial_state, _v2, v2u);

    // _v2 == x <-> _v1 == x || _v1 == -x
    for (auto x = max(0_i, initial_state.lower_bound(_v2)) ; x <= v2u ; ++x) {
        if (initial_state.in_domain(_v2, x))
            constraints.cnf(initial_state, {
                    _v2 != x,
                    initial_state.in_domain(_v1, x) ? Literal{ _v1 == x } : +constant_variable(false),
                    initial_state.in_domain(_v1, -x) ? Literal{ _v1 == -x } : +constant_variable(false) }, true);
        if (initial_state.in_domain(_v1, x))
            constraints.cnf(initial_state, {
                    _v1 != x,
                    initial_state.in_domain(_v2, x) ? Literal{ _v2 == x } : +constant_variable(false) }, true);
        if (initial_state.in_domain(_v1, -x))
            constraints.cnf(initial_state, {
                    _v1 != -x,
                    initial_state.in_domain(_v2, x) ? Literal{ _v2 == x } : +constant_variable(false) }, true);
    }
}

auto Abs::describe_for_proof() -> std::string
{
    return "abs";
}

