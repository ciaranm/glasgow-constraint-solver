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
    if (initial_state.lower_bound(_v2) < 0_i)
        constraints.cnf({ _v2 >= 0_i }, true);

    // _v1 <= upper_bound(_v2)
    if (initial_state.upper_bound(_v1) > initial_state.upper_bound(_v2))
        constraints.cnf({ _v1 < initial_state.upper_bound(_v2) + 1_i }, true);

    // _v1 >= -upper_bound(_v2)
    if (initial_state.upper_bound(_v1) < -initial_state.upper_bound(_v2))
        constraints.cnf({ _v1 >= -initial_state.upper_bound(_v2) }, true);

    // _v2 <= max(upper_bound(_v1), -lower_bound(_v1))
    auto v2u = max(initial_state.upper_bound(_v1), -initial_state.lower_bound(_v1));
    if (initial_state.upper_bound(_v2) > v2u)
        constraints.cnf({ _v2 < v2u + 1_i }, true);

    // _v2 == x <-> _v1 == x || _v1 == -x
    for (auto x = max(0_i, initial_state.lower_bound(_v2)) ; x <= v2u ; ++x) {
        constraints.cnf({ _v2 != x, _v1 == x, _v1 == -x }, true);
        constraints.cnf({ _v1 != x, _v2 == x }, true);
        constraints.cnf({ _v1 != -x, _v2 == x }, true);
    }
}

auto Abs::describe_for_proof() -> std::string
{
    return "abs";
}

