/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/equals.hh>
#include <gcs/low_level_constraint_store.hh>
#include <gcs/state.hh>

#include "util/overloaded.hh"

using namespace gcs;

using std::min;
using std::max;
using std::visit;

Equals::Equals(const IntegerVariableID v1, const IntegerVariableID v2, const BooleanVariableID cond) :
    _v1(v1),
    _v2(v2),
    _cond(cond)
{
}

Equals::Equals(const IntegerVariableID v1, const IntegerVariableID v2, bool cond) :
    _v1(v1),
    _v2(v2),
    _cond(cond)
{
}

auto Equals::convert_to_low_level(LowLevelConstraintStore & constraints, const State & initial_state) && -> void
{
    auto lower_common = max(initial_state.lower_bound(_v1), initial_state.lower_bound(_v2));
    auto upper_common = min(initial_state.upper_bound(_v1), initial_state.upper_bound(_v2));

    visit(overloaded(
                [&] (const BooleanVariableID cond) {
                    // _v1 < lower_common -> !cond, _v2 < lower_common -> !cond, _v1 > upper_common -> ! cond, _v2 > upper_common -> ! cond
                    if (initial_state.lower_bound(_v1) < lower_common)
                        constraints.cnf({ { _v1 >= lower_common }, { ! cond } });
                    if (initial_state.lower_bound(_v2) < lower_common)
                        constraints.cnf({ { _v2 >= lower_common }, { ! cond } });
                    if (initial_state.upper_bound(_v1) > upper_common)
                        constraints.cnf({ { _v1 < upper_common + 1_i }, { ! cond } });
                    if (initial_state.upper_bound(_v2) > upper_common)
                        constraints.cnf({ { _v2 < upper_common + 1_i }, { ! cond } });

                    // (*cond and _v1 == v) -> _v2 == v
                    for (auto v = lower_common ; v <= upper_common ; ++v)
                        constraints.cnf( { { _v1 != v }, { _v2 == v }, { ! cond } });

                    // (! *cond and _v1 == v) -> _v2 != v
                    for (auto v = lower_common ; v <= upper_common ; ++v)
                        constraints.cnf( { { + cond }, { _v1 != v }, { _v2 != v } } );
                },
                [&] (const bool cond) {
                    if (cond) {
                        if (initial_state.lower_bound(_v1) < lower_common)
                            constraints.cnf({ { _v1 >= lower_common } });
                        if (initial_state.lower_bound(_v2) < lower_common)
                            constraints.cnf({ { _v2 >= lower_common } });
                        if (initial_state.upper_bound(_v1) > upper_common)
                            constraints.cnf({ { _v1 < upper_common + 1_i } });
                        if (initial_state.upper_bound(_v2) > upper_common)
                            constraints.cnf({ { _v2 < upper_common + 1_i } });

                        for (auto v = lower_common ; v <= upper_common ; ++v)
                            constraints.cnf( { { _v1 != v }, { _v2 == v } });

                        for (auto v = lower_common ; v <= upper_common ; ++v)
                            constraints.cnf( { { _v1 == v }, { _v2 != v } } );
                    }
                    else {
                        for (auto v = lower_common ; v <= upper_common ; ++v)
                            constraints.cnf( { { _v1 != v }, { _v2 != v } });
                    }
                }
    ), _cond);
}

