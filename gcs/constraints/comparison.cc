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
using std::pair;
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

    bool use_special_not_equals = _full_reif && LiteralIs::DefinitelyFalse == initial_state.test_literal(_cond);
    bool use_special_equals_iff = _full_reif && LiteralIs::Undecided == initial_state.test_literal(_cond);
    bool use_special_equals_if = (! _full_reif) && LiteralIs::Undecided == initial_state.test_literal(_cond);
    bool use_cnf = ! (use_special_not_equals || use_special_equals_iff || use_special_equals_if);

    if (use_special_not_equals) {
        Triggers triggers;
        triggers.on_instantiated = { _v1, _v2 };

        propagators.propagator(initial_state, [v1 = _v1, v2 = _v2] (State & state) -> pair<Inference, PropagatorState> {
                auto value1 = state.optional_single_value(v1);
                auto value2 = state.optional_single_value(v2);
                if (value1 && value2)
                    return pair{ (*value1 != *value2) ? Inference::NoChange : Inference::Contradiction, PropagatorState::DisableUntilBacktrack };
                else if (value1)
                    return pair{ state.infer(v2 != *value1, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                else if (value2)
                    return pair{ state.infer(v1 != *value2, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                else
                    return pair{ Inference::NoChange, PropagatorState::Enable };
                }, triggers, "not equal");
    }

    if (use_special_equals_iff) {
        Triggers triggers;
        triggers.on_change = { _v1, _v2 };
        visit(overloaded{
                [&] (const LiteralFromIntegerVariable & v) { triggers.on_instantiated.push_back(v.var); },
                [&] (const TrueLiteral &) { },
                [&] (const FalseLiteral &) { }
                }, _cond);

        propagators.propagator(initial_state, [v1 = _v1, v2 = _v2, cond = _cond] (State & state) -> pair<Inference, PropagatorState> {
                switch (state.test_literal(cond)) {
                    case LiteralIs::DefinitelyTrue: {
                        // condition is true, force equality
                        auto value1 = state.optional_single_value(v1);
                        if (value1)
                            return pair{ state.infer(v2 == *value1, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };

                        auto value2 = state.optional_single_value(v2);
                        if (value2)
                            return pair{ state.infer(v1 == *value2, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };

                        auto result = Inference::NoChange;

                        // restrict to intersection
                        state.for_each_value_while(v1, [&] (Integer val) {
                                if (! state.in_domain(v2, val))
                                    increase_inference_to(result, state.infer(v1 != val, NoJustificationNeeded{ }));
                                return result != Inference::Contradiction;
                                });

                        state.for_each_value_while(v2, [&] (Integer val) {
                                if (! state.in_domain(v1, val))
                                    increase_inference_to(result, state.infer(v2 != val, NoJustificationNeeded{ }));
                                return result != Inference::Contradiction;
                                });

                        return pair{ result, PropagatorState::Enable };
                    }
                    break;

                    case LiteralIs::DefinitelyFalse: {
                        // condition is false, force inequality
                        auto value1 = state.optional_single_value(v1);
                        auto value2 = state.optional_single_value(v2);
                        if (value1 && value2)
                            return pair{ (*value1 != *value2) ? Inference::NoChange : Inference::Contradiction, PropagatorState::DisableUntilBacktrack };
                        else if (value1)
                            return pair{ state.infer(v2 != *value1, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                        else if (value2)
                            return pair{ state.infer(v1 != *value2, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                        else
                            return pair{ Inference::NoChange, PropagatorState::Enable };
                    }
                    break;

                    case LiteralIs::Undecided: {
                        // condition is undecided, are we in a situation where it's now forced?
                        auto value1 = state.optional_single_value(v1);
                        auto value2 = state.optional_single_value(v2);
                        if (value1 && value2) {
                            return pair{ state.infer(*value1 == *value2 ? cond : ! cond,
                                    NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                        }
                        else if (value1) {
                            if (! state.in_domain(v2, *value1))
                                return pair{ state.infer(! cond, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                            else
                                return pair{ Inference::NoChange, PropagatorState::Enable };
                        }
                        else if (value2) {
                            if (! state.in_domain(v1, *value2))
                                return pair{ state.infer(! cond, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                            else
                                return pair{ Inference::NoChange, PropagatorState::Enable };
                        }
                        else {
                            // not equals is forced if there's no overlap between domains
                            bool overlap = false;
                            state.for_each_value_while(v1, [&] (Integer val) {
                                    if (state.in_domain(v2, val))
                                        overlap = true;
                                    return ! overlap;
                                    });

                            if (! overlap)
                                return pair{ state.infer(! cond, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                            else
                                return pair{ Inference::NoChange, PropagatorState::Enable };
                        }
                    }
                    break;
                }

                throw NonExhaustiveSwitch{ };
            }, triggers, "equals iff");
    }

    if (use_special_equals_if) {
        Triggers triggers;
        triggers.on_change = { _v1, _v2 };
        visit(overloaded{
                [&] (const LiteralFromIntegerVariable & v) { triggers.on_instantiated.push_back(v.var); },
                [&] (const TrueLiteral &) { },
                [&] (const FalseLiteral &) { }
                }, _cond);

        propagators.propagator(initial_state, [v1 = _v1, v2 = _v2, cond = _cond] (State & state) -> pair<Inference, PropagatorState> {
                switch (state.test_literal(cond)) {
                    case LiteralIs::DefinitelyTrue: {
                        // condition is true, force equality
                        auto value1 = state.optional_single_value(v1);
                        if (value1)
                            return pair{ state.infer(v2 == *value1, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };

                        auto value2 = state.optional_single_value(v2);
                        if (value2)
                            return pair{ state.infer(v1 == *value2, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };

                        auto result = Inference::NoChange;

                        // restrict to intersection
                        state.for_each_value_while(v1, [&] (Integer val) {
                                if (! state.in_domain(v2, val))
                                    increase_inference_to(result, state.infer(v1 != val, NoJustificationNeeded{ }));
                                return result != Inference::Contradiction;
                                });

                        state.for_each_value_while(v2, [&] (Integer val) {
                                if (! state.in_domain(v1, val))
                                    increase_inference_to(result, state.infer(v2 != val, NoJustificationNeeded{ }));
                                return result != Inference::Contradiction;
                                });

                        return pair{ result, PropagatorState::Enable };
                    }
                    break;

                    case LiteralIs::DefinitelyFalse: {
                        return pair{ Inference::NoChange, PropagatorState::Enable };
                    }
                    break;

                    case LiteralIs::Undecided: {
                        // condition is undecided, are we in a situation where it's now forced?
                        auto value1 = state.optional_single_value(v1);
                        auto value2 = state.optional_single_value(v2);
                        if (value1 && value2) {
                            if (*value1 != *value2)
                                return pair{ state.infer(! cond, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                            else
                                return pair{ Inference::NoChange, PropagatorState::DisableUntilBacktrack };
                        }
                        else if (value1) {
                            if (! state.in_domain(v2, *value1))
                                return pair{ state.infer(! cond, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                            else
                                return pair{ Inference::NoChange, PropagatorState::Enable };
                        }
                        else if (value2) {
                            if (! state.in_domain(v1, *value2))
                                return pair{ state.infer(! cond, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                            else
                                return pair{ Inference::NoChange, PropagatorState::Enable };
                        }
                        else {
                            // not equals is forced if there's no overlap between domains
                            bool overlap = false;
                            state.for_each_value_while(v1, [&] (Integer val) {
                                    if (state.in_domain(v2, val))
                                        overlap = true;
                                    return ! overlap;
                                    });

                            if (! overlap)
                                return pair{ state.infer(! cond, NoJustificationNeeded{ }), PropagatorState::DisableUntilBacktrack };
                            else
                                return pair{ Inference::NoChange, PropagatorState::Enable };
                        }
                    }
                    break;
                }

                throw NonExhaustiveSwitch{ };
            }, triggers, "equals if");
    }

    if (use_cnf || propagators.want_nonpropagating()) {
        // _v1 < lower_common -> !cond, _v2 < lower_common -> !cond, _v1 > upper_common -> ! cond, _v2 > upper_common -> ! cond
        if (initial_state.lower_bound(_v1) < lower_common)
            propagators.cnf(initial_state, { { _v1 >= lower_common }, { ! _cond } }, use_cnf);
        if (initial_state.lower_bound(_v2) < lower_common)
            propagators.cnf(initial_state, { { _v2 >= lower_common }, { ! _cond } }, use_cnf);
        if (initial_state.upper_bound(_v1) > upper_common)
            propagators.cnf(initial_state, { { _v1 < upper_common + 1_i }, { ! _cond } }, use_cnf);
        if (initial_state.upper_bound(_v2) > upper_common)
            propagators.cnf(initial_state, { { _v2 < upper_common + 1_i }, { ! _cond } }, use_cnf);

        // (cond and _v1 == v) -> _v2 == v
        for (auto v = lower_common ; v <= upper_common ; ++v)
            propagators.cnf(initial_state, { { _v1 != v }, { _v2 == v }, { ! _cond } }, use_cnf);

        // (! cond and _v1 == v) -> _v2 != v
        if (_full_reif)
            for (auto v = lower_common ; v <= upper_common ; ++v)
                propagators.cnf(initial_state, { { _cond }, { _v1 != v }, { _v2 != v } }, use_cnf);
    }
}

auto ComparisonReif::_install_less_than(Propagators & propagators, const State & initial_state, bool equal) && -> void
{
    bool use_special_less = _full_reif && LiteralIs::DefinitelyTrue == initial_state.test_literal(_cond);
    bool use_cnf = ! use_special_less;

    if (use_special_less) {
        Triggers triggers;
        triggers.on_instantiated = { _v1, _v2 };

        propagators.propagator(initial_state, [v1 = _v1, v2 = _v2, equal = equal] (State & state) -> pair<Inference, PropagatorState> {
                auto result = Inference::NoChange;
                increase_inference_to(result, state.infer(v1 < state.upper_bound(v2) + (equal ? 1_i : 0_i), NoJustificationNeeded{ }));
                if (result != Inference::Contradiction)
                    increase_inference_to(result, state.infer(v2 >= state.lower_bound(v1) + (equal ? 0_i : 1_i), NoJustificationNeeded{ }));
                return pair{ result, PropagatorState::Enable };
                }, triggers, "less");
    }

    if (use_cnf || propagators.want_nonpropagating()) {
        // cond -> (v2 == v -> v1 op v)
        for (auto v = initial_state.lower_bound(_v2) ; v <= initial_state.upper_bound(_v2) ; ++v) {
            auto bound = equal ? v + 1_i : v;
            if (initial_state.upper_bound(_v1) >= bound) {
                if (initial_state.lower_bound(_v1) <= bound)
                    propagators.cnf(initial_state, { { ! _cond }, { _v2 != v }, { _v1 < bound } }, use_cnf);
                else
                    propagators.cnf(initial_state, { { ! _cond }, { _v2 != v } }, use_cnf);
            }
        }

        // cond -> upper(v1) op upper(v2)
        auto v2u = initial_state.upper_bound(_v2) + (equal ? 1_i : 0_i);
        if (! (initial_state.upper_bound(_v1) < v2u)) {
            if (initial_state.in_domain(_v1, v2u))
                propagators.cnf(initial_state, { { ! _cond }, { _v1 < v2u } }, use_cnf);
            else
                propagators.cnf(initial_state, { { ! _cond } }, use_cnf);
        }

        if (_full_reif) {
            // !cond -> exists v. v2 == v /\ v1 !op v
            for (auto v = initial_state.lower_bound(_v2) ; v <= initial_state.upper_bound(_v2) ; ++v) {
                auto bound = equal ? v + 1_i : v;
                if (initial_state.upper_bound(_v1) >= bound) {
                    if (initial_state.lower_bound(_v1) <= bound)
                        propagators.cnf(initial_state, { { _cond }, { _v2 != v }, { _v1 >= bound } }, use_cnf);
                }
                else
                    propagators.cnf(initial_state, { { _cond }, { _v2 != v } }, use_cnf);
            }
        }
    }
}

auto ComparisonReif::describe_for_proof() -> std::string
{
    return "comparison";
}

