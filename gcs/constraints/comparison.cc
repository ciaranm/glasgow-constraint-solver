/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/comparison.hh>
#include <gcs/propagators.hh>
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

auto ComparisonReif::install(Propagators & propagators, const State & initial_state) && -> void
{
    switch (_op) {
        case ComparisonOperator::Equals:        return move(*this)._install_equals(propagators, initial_state);
        case ComparisonOperator::LessThan:      return move(*this)._install_less_than(propagators, initial_state, false);
        case ComparisonOperator::LessThanEqual: return move(*this)._install_less_than(propagators, initial_state, true);
    }
    throw NonExhaustiveSwitch{ };
}

auto ComparisonReif::_install_equals(Propagators & propagators, const State & initial_state) && -> void
{
    auto lower_common = max(initial_state.lower_bound(_v1), initial_state.lower_bound(_v2));
    auto upper_common = min(initial_state.upper_bound(_v1), initial_state.upper_bound(_v2));

    if (lower_common > upper_common) {
        propagators.cnf(initial_state, { { ! _cond } }, true);
        return;
    }

    // _v1 < lower_common -> !cond, _v2 < lower_common -> !cond, _v1 > upper_common -> ! cond, _v2 > upper_common -> ! cond
    if (initial_state.lower_bound(_v1) < lower_common)
        propagators.cnf(initial_state, { { _v1 >= lower_common }, { ! _cond } }, true);
    if (initial_state.lower_bound(_v2) < lower_common)
        propagators.cnf(initial_state, { { _v2 >= lower_common }, { ! _cond } }, true);
    if (initial_state.upper_bound(_v1) > upper_common)
        propagators.cnf(initial_state, { { _v1 < upper_common + 1_i }, { ! _cond } }, true);
    if (initial_state.upper_bound(_v2) > upper_common)
        propagators.cnf(initial_state, { { _v2 < upper_common + 1_i }, { ! _cond } }, true);

    // (cond and _v1 == v) -> _v2 == v
    for (auto v = lower_common ; v <= upper_common ; ++v)
        propagators.cnf(initial_state, { { _v1 != v }, { _v2 == v }, { ! _cond } }, true);

    // (! cond and _v1 == v) -> _v2 != v
    if (_full_reif)
        for (auto v = lower_common ; v <= upper_common ; ++v)
            propagators.cnf(initial_state, { { _cond }, { _v1 != v }, { _v2 != v } }, true);
}

auto ComparisonReif::_install_less_than(Propagators & propagators, const State & initial_state, bool equal) && -> void
{
    // cond -> (v2 == v -> v1 op v)
    for (auto v = initial_state.lower_bound(_v2) ; v <= initial_state.upper_bound(_v2) ; ++v) {
        auto bound = equal ? v + 1_i : v;
        if (initial_state.upper_bound(_v1) >= bound) {
            if (initial_state.lower_bound(_v1) <= bound)
                propagators.cnf(initial_state, { { ! _cond }, { _v2 != v }, { _v1 < bound } }, true);
            else
                propagators.cnf(initial_state, { { ! _cond }, { _v2 != v } }, true);
        }
    }

    // cond -> upper(v1) op upper(v2)
    auto v2u = initial_state.upper_bound(_v2) + (equal ? 1_i : 0_i);
    if (! (initial_state.upper_bound(_v1) < v2u)) {
        if (initial_state.in_domain(_v1, v2u))
            propagators.cnf(initial_state, { { ! _cond }, { _v1 < v2u } }, true);
        else
            propagators.cnf(initial_state, { { ! _cond } }, true);
    }

    if (_full_reif) {
        // !cond -> exists v. v2 == v /\ v1 !op v
        for (auto v = initial_state.lower_bound(_v2) ; v <= initial_state.upper_bound(_v2) ; ++v) {
            auto bound = equal ? v + 1_i : v;
            if (initial_state.upper_bound(_v1) >= bound) {
                if (initial_state.lower_bound(_v1) <= bound)
                    propagators.cnf(initial_state, { { _cond }, { _v2 != v }, { _v1 >= bound } }, true);
            }
            else
                propagators.cnf(initial_state, { { _cond }, { _v2 != v } }, true);
        }
    }
}

auto ComparisonReif::describe_for_proof() -> std::string
{
    return "comparison";
}

