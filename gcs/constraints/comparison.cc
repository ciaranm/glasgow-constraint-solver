#include <gcs/constraints/comparison.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::pair;
using std::unique_ptr;

CompareLessThanReif::CompareLessThanReif(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond, bool full_reif, bool or_equal) :
    _v1(v1),
    _v2(v2),
    _cond(cond),
    _full_reif(full_reif),
    _or_equal(or_equal)
{
}

auto CompareLessThanReif::clone() const -> unique_ptr<Constraint>
{
    return make_unique<CompareLessThanReif>(_v1, _v2, _cond, _full_reif, _or_equal);
}

auto CompareLessThanReif::install(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) && -> void
{
    if (optional_model) {
        auto do_less = [&](IntegerVariableID v1, IntegerVariableID v2, optional<HalfReifyOnConjunctionOf> cond, bool or_equal) {
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * v1 + -1_i * v2 <= (or_equal ? 0_i : -1_i), cond);
        };

        overloaded{
            [&](const TrueLiteral &) {
                do_less(_v1, _v2, nullopt, _or_equal);
            },
            [&](const FalseLiteral &) {
                do_less(_v2, _v1, nullopt, ! _or_equal);
            },
            [&](const IntegerVariableCondition & cond) {
                do_less(_v1, _v2, HalfReifyOnConjunctionOf{{cond}}, _or_equal);
                if (_full_reif)
                    do_less(_v2, _v1, HalfReifyOnConjunctionOf{{! cond}}, ! _or_equal);
            }}
            .visit(_cond);
    }

    auto v1_is_constant = initial_state.optional_single_value(_v1);
    auto v2_is_constant = initial_state.optional_single_value(_v2);
    auto cond_is = initial_state.test_literal(_cond);

    if (v1_is_constant && v2_is_constant) {
        switch (cond_is) {
        case LiteralIs::Undecided:
            propagators.install([v1 = _v1, v2 = _v2, v1_is_constant = v1_is_constant, v2_is_constant = v2_is_constant,
                                    cond = _cond, or_equal = _or_equal, full_reif = _full_reif](
                                    const State &, auto & inference) {
                auto actual = (or_equal ? *v1_is_constant <= *v2_is_constant : *v1_is_constant < *v2_is_constant);
                if (actual && full_reif) {
                    inference.infer(cond, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 == *v1_is_constant, v2 == *v2_is_constant}}; }});
                    return PropagatorState::DisableUntilBacktrack;
                }
                else if (! actual) {
                    inference.infer(! cond, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 == *v1_is_constant, v2 == *v2_is_constant}}; }});
                    return PropagatorState::DisableUntilBacktrack;
                }
                else
                    return PropagatorState::DisableUntilBacktrack;
            },
                Triggers{}, "compare less than reif");
            break;

        case LiteralIs::DefinitelyTrue:
            if (! (_or_equal
                        ? *v1_is_constant <= *v2_is_constant
                        : *v1_is_constant < *v2_is_constant))
                propagators.model_contradiction(initial_state, optional_model, "CompareLessThanReif with true condition violated");
            break;

        case LiteralIs::DefinitelyFalse:
            if (_full_reif && (_or_equal ? *v1_is_constant <= *v2_is_constant : *v1_is_constant < *v2_is_constant))
                propagators.model_contradiction(initial_state, optional_model, "CompareLessThanReif with false condition violated");
            break;
        }
        return;
    }

    if (v1_is_constant && (LiteralIs::DefinitelyTrue == cond_is || (_full_reif && LiteralIs::DefinitelyFalse == cond_is))) {
        propagators.install([v1_is_constant = *v1_is_constant, v1 = _v1, v2 = _v2, or_equal = _or_equal, cond = _cond, cond_is = cond_is](
                                const State &, auto & inference) -> PropagatorState {
            if (cond_is == LiteralIs::DefinitelyTrue) {
                inference.infer_greater_than_or_equal(v2, or_equal ? v1_is_constant : v1_is_constant + 1_i,
                    JustifyUsingRUP{}, Reason{[=]() { return Literals{{cond, v1 >= v1_is_constant}}; }});
                return PropagatorState::DisableUntilBacktrack;
            }
            else {
                inference.infer_less_than(v2, or_equal ? v1_is_constant : v1_is_constant - 1_i, JustifyUsingRUP{},
                    Reason{[=]() { return Literals{{cond, v1 < v1_is_constant + 1_i}}; }});
                return PropagatorState::DisableUntilBacktrack;
            }
        },
            Triggers{}, "compare less than reif");
    }

    if (v2_is_constant && (LiteralIs::DefinitelyTrue == cond_is || (_full_reif && LiteralIs::DefinitelyFalse == cond_is))) {
        propagators.install([v2_is_constant = *v2_is_constant, v1 = _v1, v2 = _v2, or_equal = _or_equal, cond = _cond, cond_is = cond_is](
                                const State &, auto & inference) -> PropagatorState {
            if (cond_is == LiteralIs::DefinitelyTrue) {
                inference.infer_less_than(v1, or_equal ? v2_is_constant + 1_i : v2_is_constant, JustifyUsingRUP{},
                    Reason{[=]() { return Literals{{cond, v2 < v2_is_constant + 1_i}}; }});
                return PropagatorState::DisableUntilBacktrack;
            }
            else {
                inference.infer_greater_than_or_equal(v1, or_equal ? v2_is_constant + 1_i : v2_is_constant,
                    JustifyUsingRUP{}, Reason{[=]() { return Literals{{cond, v2 >= v2_is_constant}}; }});
                return PropagatorState::DisableUntilBacktrack;
            }
        },
            Triggers{}, "compare less than reif");
    }

    // if we get this far, none of the special cases apply

    Triggers triggers{.on_bounds = {_v1, _v2}};
    overloaded{
        [&](const TrueLiteral &) {},
        [&](const FalseLiteral &) {},
        [&](const IntegerVariableCondition & cond) { triggers.on_change.push_back(cond.var); }}
        .visit(_cond);

    visit([&](auto & _v1, auto & _v2, auto & _cond) {
        propagators.install([v1 = _v1, v2 = _v2, cond = _cond, full_reif = _full_reif, or_equal = _or_equal](
                                const State & state, auto & inference) -> PropagatorState {
            auto cond_is = state.test_literal(cond);
            switch (cond_is) {
            case LiteralIs::DefinitelyTrue: {
                auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                inference.infer_less_than(v1, v2_bounds.second + (or_equal ? 1_i : 0_i), JustifyUsingRUP{}, Reason{[=]() { return Literals{{cond, v2 < v2_bounds.second + 1_i}}; }});
                inference.infer_greater_than_or_equal(v2, v1_bounds.first + (or_equal ? 0_i : 1_i), JustifyUsingRUP{}, Reason{[=]() { return Literals{{cond, v1 >= v1_bounds.first}}; }});
                return v1_bounds.second < (v2_bounds.first + (or_equal ? 1_i : 0_i)) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
            } break;

            case LiteralIs::DefinitelyFalse:
                if (full_reif) {
                    auto v2_lower = state.lower_bound(v2);
                    inference.infer_greater_than_or_equal(v1, v2_lower + (or_equal ? 1_i : 0_i),
                        JustifyUsingRUP{}, Reason{[=]() { return Literals{{! cond, v2 >= v2_lower}}; }});
                    return PropagatorState::Enable;
                }
                else
                    return PropagatorState::DisableUntilBacktrack;
                break;

            case LiteralIs::Undecided:
                if (full_reif && (or_equal ? state.upper_bound(v1) <= state.lower_bound(v2) : state.upper_bound(v1) < state.lower_bound(v2))) {
                    auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                    inference.infer(cond, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 < v1_bounds.second + 1_i, v2 >= v2_bounds.first}}; }});
                    return PropagatorState::Enable;
                }
                else if (or_equal
                        ? state.lower_bound(v1) > state.upper_bound(v2)
                        : state.lower_bound(v1) >= state.upper_bound(v2)) {
                    auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                    inference.infer(! cond, JustifyUsingRUP{}, Reason{[=]() { return Literals{{v1 >= v1_bounds.first, v2 < v2_bounds.second + 1_i}}; }});
                    return PropagatorState::Enable;
                }
                else
                    return PropagatorState::Enable;
                break;
            }

            throw NonExhaustiveSwitch{};
        },
            triggers, "compare less than reif");
    },
        _v1, _v2, _cond);
}

auto CompareLessThanReif::describe_for_proof() -> std::string
{
    return "compare less than reif";
}
