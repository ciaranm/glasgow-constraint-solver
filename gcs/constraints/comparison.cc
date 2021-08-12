/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/comparison.hh>
#include <gcs/low_level_constraint_store.hh>
#include <gcs/state.hh>
#include <gcs/exception.hh>

#include "util/overloaded.hh"

using namespace gcs;

using std::max;
using std::min;
using std::move;
using std::visit;

ComparisonReif::ComparisonReif(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond, bool full_reif, ComparisonOperator op) :
    _v1(v1),
    _v2(v2),
    _cond(cond),
    _full_reif(full_reif),
    _op(op)
{
}

auto ComparisonReif::convert_to_low_level(LowLevelConstraintStore & constraints, const State & initial_state) && -> void
{
    switch (_op) {
        case ComparisonOperator::Equals:        return move(*this)._convert_to_low_level_equals(constraints, initial_state);
        case ComparisonOperator::LessThan:      return move(*this)._convert_to_low_level_less_than(constraints, initial_state, false);
        case ComparisonOperator::LessThanEqual: return move(*this)._convert_to_low_level_less_than(constraints, initial_state, true);
    }
    throw NonExhaustiveSwitch{ };
}

auto ComparisonReif::_convert_to_low_level_equals(LowLevelConstraintStore & constraints, const State & initial_state) && -> void
{
    auto lower_common = max(initial_state.lower_bound(_v1), initial_state.lower_bound(_v2));
    auto upper_common = min(initial_state.upper_bound(_v1), initial_state.upper_bound(_v2));

    // _v1 < lower_common -> !cond, _v2 < lower_common -> !cond, _v1 > upper_common -> ! cond, _v2 > upper_common -> ! cond
    if (_full_reif) {
        if (initial_state.lower_bound(_v1) < lower_common)
            constraints.cnf({ { _v1 >= lower_common }, { ! _cond } }, true);
        if (initial_state.lower_bound(_v2) < lower_common)
            constraints.cnf({ { _v2 >= lower_common }, { ! _cond } }, true);
        if (initial_state.upper_bound(_v1) > upper_common)
            constraints.cnf({ { _v1 < upper_common + 1_i }, { ! _cond } }, true);
        if (initial_state.upper_bound(_v2) > upper_common)
            constraints.cnf({ { _v2 < upper_common + 1_i }, { ! _cond } }, true);
    }

    // (*cond and _v1 == v) -> _v2 == v
    for (auto v = lower_common ; v <= upper_common ; ++v)
        constraints.cnf( { { _v1 != v }, { _v2 == v }, { ! _cond } }, true);

    // (! *cond and _v1 == v) -> _v2 != v
    if (_full_reif)
        for (auto v = lower_common ; v <= upper_common ; ++v)
            constraints.cnf( { { _cond }, { _v1 != v }, { _v2 != v } }, true);
}

auto ComparisonReif::_convert_to_low_level_less_than(LowLevelConstraintStore & constraints, const State & initial_state, bool equal) && -> void
{
    if (! _full_reif)
        throw UnimplementedException{ };

    for (auto v = initial_state.lower_bound(_v2) ; v <= initial_state.upper_bound(_v2) ; ++v)
        constraints.cnf({ { ! _cond }, { _v2 != v }, { _v1 < (equal ? v + 1_i : v) } }, true);
}

auto ComparisonReif::describe_for_proof() -> std::string
{
    return "comparison";
}

