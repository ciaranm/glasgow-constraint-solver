/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/comparison.hh>
#include <gcs/detail/propagators.hh>
#include <gcs/detail/state.hh>
#include <gcs/exception.hh>

#include "util/overloaded.hh"

using namespace gcs;

using std::max;
using std::min;
using std::move;
using std::pair;

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
    case ComparisonOperator::LessThan: return move(*this)._install_less_than(propagators, initial_state, false);
    case ComparisonOperator::LessThanEqual: return move(*this)._install_less_than(propagators, initial_state, true);
    }
    throw NonExhaustiveSwitch{};
}

auto ComparisonReif::_install_less_than(Propagators & propagators, const State & initial_state, bool equal) && -> void
{
    bool use_special_less = _full_reif && LiteralIs::DefinitelyTrue == initial_state.test_literal(_cond);
    bool use_cnf = ! use_special_less;

    if (use_special_less) {
        Triggers triggers;
        triggers.on_bounds = {_v1, _v2};

        propagators.propagator(
            initial_state, [v1 = _v1, v2 = _v2, equal = equal](State & state) -> pair<Inference, PropagatorState> {
                auto result = Inference::NoChange;
                increase_inference_to(result, state.infer_less_than(v1, state.upper_bound(v2) + (equal ? 1_i : 0_i), NoJustificationNeeded{}));
                if (result != Inference::Contradiction)
                    increase_inference_to(result, state.infer_greater_than_or_equal(v2, state.lower_bound(v1) + (equal ? 0_i : 1_i), NoJustificationNeeded{}));
                return pair{result, PropagatorState::Enable};
            },
            triggers, "less");
    }

    if (use_cnf || propagators.want_nonpropagating()) {
        // cond -> (v2 == v -> v1 op v)
        for (auto v = initial_state.lower_bound(_v2); v <= initial_state.upper_bound(_v2); ++v) {
            auto bound = equal ? v + 1_i : v;
            if (initial_state.upper_bound(_v1) >= bound) {
                if (initial_state.lower_bound(_v1) <= bound)
                    propagators.cnf(initial_state, {{! _cond}, {_v2 != v}, {_v1 < bound}}, use_cnf);
                else
                    propagators.cnf(initial_state, {{! _cond}, {_v2 != v}}, use_cnf);
            }
        }

        // cond -> upper(v1) op upper(v2)
        auto v2u = initial_state.upper_bound(_v2) + (equal ? 1_i : 0_i);
        if (! (initial_state.upper_bound(_v1) < v2u)) {
            if (initial_state.in_domain(_v1, v2u))
                propagators.cnf(initial_state, {{! _cond}, {_v1 < v2u}}, use_cnf);
            else
                propagators.cnf(initial_state, {{! _cond}}, use_cnf);
        }

        if (_full_reif) {
            // !cond -> exists v. v2 == v /\ v1 !op v
            for (auto v = initial_state.lower_bound(_v2); v <= initial_state.upper_bound(_v2); ++v) {
                auto bound = equal ? v + 1_i : v;
                if (initial_state.upper_bound(_v1) >= bound) {
                    if (initial_state.lower_bound(_v1) <= bound)
                        propagators.cnf(initial_state, {{_cond}, {_v2 != v}, {_v1 >= bound}}, use_cnf);
                }
                else
                    propagators.cnf(initial_state, {{_cond}, {_v2 != v}}, use_cnf);
            }
        }
    }
}

auto ComparisonReif::describe_for_proof() -> std::string
{
    return "comparison";
}
