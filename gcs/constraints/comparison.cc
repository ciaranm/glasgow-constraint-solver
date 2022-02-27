/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/comparison.hh>
#include <gcs/detail/propagators.hh>
#include <gcs/detail/state.hh>
#include <gcs/exception.hh>

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::detail;

using std::nullopt;
using std::optional;
using std::pair;

CompareLessThanReif::CompareLessThanReif(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond, bool full_reif, bool or_equal) :
    _v1(v1),
    _v2(v2),
    _cond(cond),
    _full_reif(full_reif),
    _or_equal(or_equal)
{
}

auto CompareLessThanReif::install(Propagators & propagators, const State & initial_state) && -> void
{
    if (propagators.want_definitions()) {
        auto do_less = [&](IntegerVariableID v1, IntegerVariableID v2, optional<LiteralFromIntegerVariable> cond, bool or_equal) {
            auto cv = Linear{{1_i, v1}, {-1_i, v2}};
            propagators.define_linear_le(initial_state, cv, or_equal ? 0_i : -1_i, cond);
        };

        overloaded{
            [&](const TrueLiteral &) {
                do_less(_v1, _v2, nullopt, _or_equal);
            },
            [&](const FalseLiteral &) {
                do_less(_v2, _v1, nullopt, _or_equal);
            },
            [&](const LiteralFromIntegerVariable & ilit) {
                do_less(_v1, _v2, ilit, _or_equal);
                if (_full_reif)
                    do_less(_v2, _v1, ! ilit, ! _or_equal);
            }}
            .visit(_cond);
    }

    auto v1_is_constant = initial_state.optional_single_value(_v1);
    auto v2_is_constant = initial_state.optional_single_value(_v2);
    auto cond_is = initial_state.test_literal(_cond);

    if (v1_is_constant && v2_is_constant) {
        switch (cond_is) {
        case LiteralIs::Undecided:
            propagators.install(
                initial_state, [v1_is_constant = v1_is_constant, v2_is_constant = v2_is_constant, cond = _cond, or_equal = _or_equal, full_reif = _full_reif](State & state) {
                    auto actual = (or_equal ? *v1_is_constant <= *v2_is_constant : *v1_is_constant < *v2_is_constant);
                    if (actual && full_reif)
                        return pair{state.infer(cond, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                    else if (! actual)
                        return pair{state.infer(! cond, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
                    else
                        return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
                },
                Triggers{}, "compare less than reif");
            break;

        case LiteralIs::DefinitelyTrue:
            if (! (_or_equal
                        ? *v1_is_constant <= *v2_is_constant
                        : *v1_is_constant < *v2_is_constant))
                propagators.model_contradiction(initial_state, "CompareLessThanReif with true condition violated");
            break;

        case LiteralIs::DefinitelyFalse:
            if (_full_reif && (_or_equal ? *v1_is_constant <= *v2_is_constant : *v1_is_constant < *v2_is_constant))
                propagators.model_contradiction(initial_state, "CompareLessThanReif with false condition violated");
            break;
        }
        return;
    }

    if (v1_is_constant && (LiteralIs::DefinitelyTrue == cond_is || (_full_reif && LiteralIs::DefinitelyFalse == cond_is))) {
        propagators.install(
            initial_state, [v1_is_constant = *v1_is_constant, v2 = _v2, or_equal = _or_equal, cond_is = cond_is](State & state) -> pair<Inference, PropagatorState> {
                if (cond_is == LiteralIs::DefinitelyTrue)
                    return pair{state.infer_greater_than_or_equal(v2, or_equal ? v1_is_constant : v1_is_constant + 1_i, JustifyUsingRUP{}),
                        PropagatorState::DisableUntilBacktrack};
                else
                    return pair{state.infer_less_than(v2, or_equal ? v1_is_constant : v1_is_constant - 1_i, JustifyUsingRUP{}),
                        PropagatorState::DisableUntilBacktrack};
            },
            Triggers{}, "compare less than reif");
    }

    if (v2_is_constant && (LiteralIs::DefinitelyTrue == cond_is || (_full_reif && LiteralIs::DefinitelyFalse == cond_is))) {
        propagators.install(
            initial_state, [v2_is_constant = *v2_is_constant, v1 = _v1, or_equal = _or_equal, cond_is = cond_is](State & state) -> pair<Inference, PropagatorState> {
                if (cond_is == LiteralIs::DefinitelyTrue)
                    return pair{state.infer_less_than(v1, or_equal ? v2_is_constant + 1_i : v2_is_constant, JustifyUsingRUP{}),
                        PropagatorState::DisableUntilBacktrack};
                else
                    return pair{state.infer_greater_than_or_equal(v1, or_equal ? v2_is_constant : v2_is_constant + 1_i, JustifyUsingRUP{}),
                        PropagatorState::DisableUntilBacktrack};
            },
            Triggers{}, "compare less than reif");
    }

    // if we get this far, none of the special cases apply

    Triggers triggers{.on_bounds = {_v1, _v2}};
    overloaded{
        [&](const TrueLiteral &) {},
        [&](const FalseLiteral &) {},
        [&](const LiteralFromIntegerVariable & ilit) { triggers.on_change.push_back(ilit.var); }}
        .visit(_cond);

    visit([&](auto & _v1, auto & _v2, auto & _cond) {
        propagators.install(
            initial_state, [v1 = _v1, v2 = _v2, cond = _cond, full_reif = _full_reif, or_equal = _or_equal](State & state) -> pair<Inference, PropagatorState> {
                auto cond_is = state.test_literal(cond);
                switch (cond_is) {
                case LiteralIs::DefinitelyTrue: {
                    auto inf = Inference::NoChange;
                    increase_inference_to(inf, state.infer_less_than(v1, state.upper_bound(v2) + (or_equal ? 1_i : 0_i), JustifyUsingRUP{}));
                    if (Inference::Contradiction != inf)
                        increase_inference_to(inf, state.infer_greater_than_or_equal(v2, state.lower_bound(v1) + (or_equal ? 0_i : 1_i), JustifyUsingRUP{}));
                    return pair{inf, PropagatorState::Enable};
                } break;

                case LiteralIs::DefinitelyFalse:
                    if (full_reif)
                        return pair{state.infer_greater_than_or_equal(v1, state.lower_bound(v2) + (or_equal ? 1_i : 0_i),
                                        JustifyUsingRUP{}),
                            PropagatorState::Enable};
                    else
                        return pair{Inference::NoChange, PropagatorState::DisableUntilBacktrack};
                    break;

                case LiteralIs::Undecided:
                    if (full_reif && (or_equal ? state.upper_bound(v1) <= state.lower_bound(v2) : state.upper_bound(v1) < state.lower_bound(v2)))
                        return pair{state.infer(cond, JustifyUsingRUP{}), PropagatorState::Enable};
                    else if (or_equal
                            ? state.lower_bound(v1) > state.upper_bound(v2)
                            : state.lower_bound(v1) >= state.upper_bound(v2))
                        return pair{state.infer(! cond, JustifyUsingRUP{}), PropagatorState::Enable};
                    else
                        return pair{Inference::NoChange, PropagatorState::Enable};
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
