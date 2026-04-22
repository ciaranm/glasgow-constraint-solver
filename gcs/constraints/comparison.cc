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

ReifiedCompareLessThanOrMaybeEqual::ReifiedCompareLessThanOrMaybeEqual(const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool or_equal) :
    _v1(v1),
    _v2(v2),
    _reif_cond(cond),
    _or_equal(or_equal),
    // I don't really want to instantiate this here, but apparently I must.
    // The same thing happens in ReifiedEquals.
    evaluated_cond(evaluated_reif::Deactivated{})
{
}

auto ReifiedCompareLessThanOrMaybeEqual::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ReifiedCompareLessThanOrMaybeEqual>(_v1, _v2, _reif_cond, _or_equal);
}

auto ReifiedCompareLessThanOrMaybeEqual::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (!prepare(propagators, initial_state, optional_model)) 
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto ReifiedCompareLessThanOrMaybeEqual::define_proof_model(ProofModel & model) -> void
{
    auto do_less = [&](IntegerVariableID v1, IntegerVariableID v2, optional<HalfReifyOnConjunctionOf> cond, bool or_equal, const StringLiteral & rule) {
        model.add_constraint("ReifiedCompareLessThanOrMaybeEqual", rule, WPBSum{} + 1_i * v1 + -1_i * v2 <= (or_equal ? 0_i : -1_i), cond);
    };

    overloaded{
        [&](const reif::MustHold &) {
            do_less(_v1, _v2, nullopt, _or_equal, "condition true");
        },
        [&](const reif::MustNotHold &) {
            do_less(_v2, _v1, nullopt, ! _or_equal, "condition false");
        },
        [&](const reif::If & cond) {
            do_less(_v1, _v2, HalfReifyOnConjunctionOf{{cond.cond}}, _or_equal, "if condition");
        },
        [&](const reif::NotIf & cond) {
            do_less(_v2, _v1, HalfReifyOnConjunctionOf{{cond.cond}}, ! _or_equal, "if condition");
        },
        [&](const reif::Iff & cond) {
            do_less(_v1, _v2, HalfReifyOnConjunctionOf{{cond.cond}}, _or_equal, "if condition");
            do_less(_v2, _v1, HalfReifyOnConjunctionOf{{! cond.cond}}, ! _or_equal, "if not condition");
        }}
        .visit(_reif_cond);
}

auto ReifiedCompareLessThanOrMaybeEqual::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    v1_is_constant = initial_state.optional_single_value(_v1);
    v2_is_constant = initial_state.optional_single_value(_v2);
    evaluated_cond = initial_state.test_reification_condition(_reif_cond);
    return true;
}

auto ReifiedCompareLessThanOrMaybeEqual::install_propagators(Propagators & propagators) -> void
{
    if (v1_is_constant && v2_is_constant) {
        /* special case: both values are constant, so we're potentially forcing
         * the reification condition, or just giving contradiction, but will never
         * propagate beyond that. */
        bool holds = (_or_equal ? *v1_is_constant <= *v2_is_constant : *v1_is_constant < *v2_is_constant);
        overloaded{
            [&](const evaluated_reif::MustHold & reif) {
                if (! holds)
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = v1_is_constant, v2_is_constant = v2_is_constant, cond = reif.cond](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, ! cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{cond, v1 == *v1_is_constant, v2 == *v2_is_constant}}; }});
                    });
            },
            [&](const evaluated_reif::MustNotHold & reif) {
                if (holds)
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = v1_is_constant, v2_is_constant = v2_is_constant, cond = reif.cond](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, ! cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{cond, v1 == *v1_is_constant, v2 == *v2_is_constant}}; }});
                    });
            },
            [&](const evaluated_reif::Undecided & reif) {
                if (holds && reif.set_cond_if_must_hold)
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = v1_is_constant, v2_is_constant = v2_is_constant, cond = reif.cond](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 == *v1_is_constant, v2 == *v2_is_constant}}; }});
                    });
                else if ((holds && reif.set_not_cond_if_must_hold) || (! holds && reif.set_not_cond_if_must_not_hold))
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = v1_is_constant, v2_is_constant = v2_is_constant, cond = reif.cond](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, ! cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 == *v1_is_constant, v2 == *v2_is_constant}}; }});
                    });
            },
            [](const evaluated_reif::Deactivated &) {
            }}
            .visit(evaluated_cond);
    }
    else {
        overloaded{
            [&](const evaluated_reif::MustHold & reif) {
                Triggers triggers{.on_bounds = {_v1, _v2}};

                propagators.install([v1 = _v1, v2 = _v2, cond = reif.cond, or_equal = _or_equal](
                                        const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                    inference.infer_less_than(logger, v1, v2_bounds.second + (or_equal ? 1_i : 0_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{cond, v2 < v2_bounds.second + 1_i}}; }});
                    inference.infer_greater_than_or_equal(logger, v2, v1_bounds.first + (or_equal ? 0_i : 1_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{cond, v1 >= v1_bounds.first}}; }});
                    return v1_bounds.second < (v2_bounds.first + (or_equal ? 1_i : 0_i)) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
                },
                    triggers, "reified compare less than or maybe equal");
            },
            [&](const evaluated_reif::MustNotHold & reif) {
                Triggers triggers{.on_bounds = {_v1, _v2}};

                propagators.install([v1 = _v1, v2 = _v2, cond = reif.cond, or_equal = _or_equal](
                                        const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                    inference.infer_less_than(logger, v2, v1_bounds.second + (! or_equal ? 1_i : 0_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{cond, v1 < v1_bounds.second + 1_i}}; }});
                    inference.infer_greater_than_or_equal(logger, v1, v2_bounds.first + (! or_equal ? 0_i : 1_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{cond, v2 >= v2_bounds.first}}; }});
                    return v2_bounds.second < (v1_bounds.first + (! or_equal ? 1_i : 0_i)) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
                },
                    triggers, "reified compare less than or maybe equal");
            },
            [&](const evaluated_reif::Undecided & reif) {
                Triggers triggers{.on_bounds = {_v1, _v2}};
                triggers.on_change.push_back(reif.cond.var);

                propagators.install([v1 = _v1, v2 = _v2, or_equal = _or_equal, reif_cond = _reif_cond](
                                        const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    return overloaded{
                        [&](const evaluated_reif::MustHold & reif) {
                            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                            inference.infer_less_than(logger, v1, v2_bounds.second + (or_equal ? 1_i : 0_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{reif.cond, v2 < v2_bounds.second + 1_i}}; }});
                            inference.infer_greater_than_or_equal(logger, v2, v1_bounds.first + (or_equal ? 0_i : 1_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{reif.cond, v1 >= v1_bounds.first}}; }});
                            return v1_bounds.second < (v2_bounds.first + (or_equal ? 1_i : 0_i)) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
                        },
                        [&](const evaluated_reif::MustNotHold & reif) {
                            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                            inference.infer_less_than(logger, v2, v1_bounds.second + (! or_equal ? 1_i : 0_i), JustifyUsingRUP{},
                                ReasonFunction{[=]() { return Reason{{reif.cond, v1 < v1_bounds.second + 1_i}}; }});
                            inference.infer_greater_than_or_equal(logger, v1, v2_bounds.first + (! or_equal ? 0_i : 1_i), JustifyUsingRUP{},
                                ReasonFunction{[=]() { return Reason{{reif.cond, v2 >= v2_bounds.first}}; }});
                            return v2_bounds.second < (v1_bounds.first + (! or_equal ? 1_i : 0_i)) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
                        },
                        [&](const evaluated_reif::Undecided & reif) {
                            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                            if (or_equal ? (v1_bounds.second <= v2_bounds.first) : (v1_bounds.second < v2_bounds.first)) {
                                // v1 has to be less than (or equal)
                                if (reif.set_cond_if_must_hold)
                                    inference.infer(logger, reif.cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 < v1_bounds.second + 1_i, v2 >= v2_bounds.first}}; }});
                                else if (reif.set_not_cond_if_must_hold)
                                    inference.infer(logger, ! reif.cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 < v1_bounds.second + 1_i, v2 >= v2_bounds.first}}; }});
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else if (or_equal ? (v1_bounds.first > v2_bounds.second) : (v1_bounds.first >= v2_bounds.second)) {
                                // v1 has to be greater than (or equal)
                                if (reif.set_not_cond_if_must_not_hold)
                                    inference.infer(logger, ! reif.cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 >= v1_bounds.first, v2 < v2_bounds.second + 1_i}}; }});
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else
                                return PropagatorState::Enable;
                        },
                        [&](const evaluated_reif::Deactivated &) {
                            return PropagatorState::DisableUntilBacktrack;
                        }}
                        .visit(state.test_reification_condition(reif_cond));
                },
                    triggers, "reified compare less than or maybe equal");
            },
            [](const evaluated_reif::Deactivated &) {
            }}
            .visit(evaluated_cond);
    }
}
