/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/low_level_constraint_store.hh>
#include <gcs/state.hh>

#include <util/for_each.hh>

#include <algorithm>

using namespace gcs;

using std::min;
using std::max;
using std::vector;

AllDifferent::AllDifferent(const vector<IntegerVariableID> & v) :
    _vars(move(v))
{
}

auto AllDifferent::convert_to_low_level(LowLevelConstraintStore & constraints, const State & initial_state) && -> void
{
    // for each distinct pair of variables...
    for_each_distinct_pair(_vars, [&] (auto v, auto w) {
        // for each value in both domains...
        auto lower = max(initial_state.lower_bound(v), initial_state.lower_bound(w));
        auto upper = min(initial_state.upper_bound(v), initial_state.upper_bound(w));
        for ( ; lower <= upper ; ++lower)
            if (initial_state.in_domain(v, lower) && initial_state.in_domain(w, lower)) {
                // can't have both variables taking that value
                constraints.cnf({ v != lower, w != lower });
            }
    });
}

