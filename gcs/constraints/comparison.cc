#include <gcs/constraints/comparison.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <fmt/ostream.h>

#include <sstream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::pair;
using std::unique_ptr;
using std::string;
using std::stringstream;

using fmt::print;

ReifiedCompareLessThanOrMaybeEqual::ReifiedCompareLessThanOrMaybeEqual(const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool or_equal, bool vars_swapped) :
    _v1(v1),
    _v2(v2),
    _reif_cond(cond),
    _or_equal(or_equal),
    _vars_swapped(vars_swapped)
{
}

auto ReifiedCompareLessThanOrMaybeEqual::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ReifiedCompareLessThanOrMaybeEqual>(_v1, _v2, _reif_cond, _or_equal, _vars_swapped);
}

auto ReifiedCompareLessThanOrMaybeEqual::install(Propagators & propagators, State & initial_state,
    ProofModel * const optional_model) && -> void
{
    if (optional_model) {
        auto do_less = [&](IntegerVariableID v1, IntegerVariableID v2, optional<HalfReifyOnConjunctionOf> cond, bool or_equal, const StringLiteral & rule) {
            optional_model->add_constraint("ReifiedCompareLessThanOrMaybeEqual", rule, WPBSum{} + 1_i * v1 + -1_i * v2 <= (or_equal ? 0_i : -1_i), cond);
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

    auto v1_is_constant = initial_state.optional_single_value(_v1);
    auto v2_is_constant = initial_state.optional_single_value(_v2);

    if (v1_is_constant && v2_is_constant) {
        /* special case: both values are constant, so we're potentially forcing
         * the reification condition, or just giving contradiction, but will never
         * propagate beyond that. */
        bool holds = (_or_equal ? *v1_is_constant <= *v2_is_constant : *v1_is_constant < *v2_is_constant);
        overloaded{
            [&](const evaluated_reif::MustHold & reif) {
                if (! holds)
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = v1_is_constant, v2_is_constant = v2_is_constant, cond = reif.cond ? Literal{! *reif.cond} : FalseLiteral{}](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 == *v1_is_constant, v2 == *v2_is_constant}}; }});
                    });
            },
            [&](const evaluated_reif::MustNotHold & reif) {
                if (holds)
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = v1_is_constant, v2_is_constant = v2_is_constant, inv_cond = reif.cond ? Literal{*reif.cond} : FalseLiteral{}](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, inv_cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 == *v1_is_constant, v2 == *v2_is_constant}}; }});
                    });
            },
            [&](const evaluated_reif::Undecided & reif) {
                if (holds && reif.set_cond_if_must_hold)
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = v1_is_constant, v2_is_constant = v2_is_constant, cond = reif.cond](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 == *v1_is_constant, v2 == *v2_is_constant}}; }});
                    });
                else if ((holds && reif.set_not_cond_if_must_hold) || (! holds && reif.set_not_cond_if_must_not_hold))
                    propagators.install_initialiser([v1 = _v1, v2 = _v2, v1_is_constant = v1_is_constant, v2_is_constant = v2_is_constant, inv_cond = ! reif.cond](
                                                        const State &, auto & inference, ProofLogger * const logger) -> void {
                        inference.infer(logger, inv_cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 == *v1_is_constant, v2 == *v2_is_constant}}; }});
                    });
            },
            [](const evaluated_reif::Deactivated &) {
            }}
            .visit(initial_state.test_reification_condition(_reif_cond));
    }
    else {
        overloaded{
            [&](const evaluated_reif::MustHold & reif) {
                Triggers triggers{.on_bounds = {_v1, _v2}};

                propagators.install([v1 = _v1, v2 = _v2, cond = reif.cond ? Literal{*reif.cond} : TrueLiteral{}, or_equal = _or_equal](
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

                propagators.install([v1 = _v1, v2 = _v2, inv_cond = reif.cond ? Literal{! *reif.cond} : TrueLiteral{}, or_equal = _or_equal](
                                        const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                    inference.infer_less_than(logger, v2, v1_bounds.second + (! or_equal ? 1_i : 0_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{inv_cond, v1 < v1_bounds.second + 1_i}}; }});
                    inference.infer_greater_than_or_equal(logger, v1, v2_bounds.first + (! or_equal ? 0_i : 1_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{inv_cond, v2 >= v2_bounds.first}}; }});
                    return v2_bounds.second < (v1_bounds.first + (! or_equal ? 1_i : 0_i)) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
                },
                    triggers, "reified compare less than or maybe equal");
            },
            [&](const evaluated_reif::Undecided & reif) {
                Triggers triggers{.on_bounds = {_v1, _v2}};
                triggers.on_change.push_back(reif.cond.var);

                propagators.install([v1 = _v1, v2 = _v2, or_equal = _or_equal, reif_cond = _reif_cond, outer_cond = reif.cond](
                                        const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    return overloaded{
                        [&](const evaluated_reif::MustHold &) {
                            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                            inference.infer_less_than(logger, v1, v2_bounds.second + (or_equal ? 1_i : 0_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{outer_cond, v2 < v2_bounds.second + 1_i}}; }});
                            inference.infer_greater_than_or_equal(logger, v2, v1_bounds.first + (or_equal ? 0_i : 1_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{outer_cond, v1 >= v1_bounds.first}}; }});
                            return v1_bounds.second < (v2_bounds.first + (or_equal ? 1_i : 0_i)) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
                        },
                        [&](const evaluated_reif::MustNotHold &) {
                            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                            inference.infer_less_than(logger, v2, v1_bounds.second + (! or_equal ? 1_i : 0_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{! outer_cond, v1 < v1_bounds.second + 1_i}}; }});
                            inference.infer_greater_than_or_equal(logger, v1, v2_bounds.first + (! or_equal ? 0_i : 1_i), JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{! outer_cond, v2 >= v2_bounds.first}}; }});
                            return v2_bounds.second < (v1_bounds.first + (! or_equal ? 1_i : 0_i)) ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
                        },
                        [&](const evaluated_reif::Undecided & reif) {
                            auto v1_bounds = state.bounds(v1), v2_bounds = state.bounds(v2);
                            if (or_equal ? (v1_bounds.second <= v2_bounds.first) : (v1_bounds.second < v2_bounds.first)) {
                                // v1 has to be less than (or equal)
                                if (reif.set_cond_if_must_hold)
                                    inference.infer(logger, outer_cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 < v1_bounds.second + 1_i, v2 >= v2_bounds.first}}; }});
                                else if (reif.set_not_cond_if_must_hold)
                                    inference.infer(logger, ! outer_cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 < v1_bounds.second + 1_i, v2 >= v2_bounds.first}}; }});
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else if (or_equal ? (v1_bounds.first > v2_bounds.second) : (v1_bounds.first >= v2_bounds.second)) {
                                // v1 has to be greater than (or equal)
                                if (reif.set_not_cond_if_must_not_hold)
                                    inference.infer(logger, ! outer_cond, JustifyUsingRUP{}, ReasonFunction{[=]() { return Reason{{v1 >= v1_bounds.first, v2 < v2_bounds.second + 1_i}}; }});
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
            .visit(initial_state.test_reification_condition(_reif_cond));
    }
}

// ReifiedCompareLessThanOrMaybeEqual is the superclass of all the various less-than and less-than-or-equal constraints,
// so I'm hoping to be able to get away with just one s_exprify implementation here, and not have to override
// it in the subclasses. If that turns out not to be the case, I'll add overrides in the relevant subclasses
// and move this implementation to a helper function or just implement all s_expify() subclass methods.
auto ReifiedCompareLessThanOrMaybeEqual::s_exprify(const std::string & name, const ProofModel * const model) const -> std::string
{
    /*
        private:
        IntegerVariableID _v1, _v2;
        ReificationCondition _reif_cond;
        bool _full_reif;
        bool _or_equal;
        bool _vars_swapped;
    */

    // (name cmp X Y)
    // or
    // (name cmp Z X Y)
    // where cmp is
    // {{greater,less}_than{,_equal}}{,_if,_iff}

    // greater_than             reif::MustHold{}, _or_equal = false, _vars_swapped = true
    // greater_than_if          reif::If{},       _or_equal = false, _vars_swapped = true
    // greater_than_iff         reif::Iff{},      _or_equal = false, _vars_swapped = true
    // greater_than_equal       reif::MustHold{}, _or_equal = true,  _vars_swapped = true
    // greater_than_equal_if    reif::If{},       _or_equal = true,  _vars_swapped = true
    // greater_than_equal_iff   reif::Iff{},      _or_equal = true,  _vars_swapped = true
    // less_than                reif::MustHold{}, _or_equal = false, _vars_swapped = false
    // less_than_if             reif::If{},       _or_equal = false, _vars_swapped = false
    // less_than_iff            reif::Iff{},      _or_equal = false, _vars_swapped = false
    // less_than_equal          reif::MustHold{}, _or_equal = true,  _vars_swapped = false
    // less_than_equal_if       reif::If{},       _or_equal = true,  _vars_swapped = false
    // less_than_equal_iff      reif::Iff{},      _or_equal = true,  _vars_swapped = false

    stringstream s;

    auto reif = overloaded{
            [&](const reif::MustHold &) -> string { return ""; },
            [&](const reif::If &)       -> string { return "_if"; },
            [&](const reif::Iff &)      -> string { return "_iff"; },
            [&](const auto &) -> string { throw UnexpectedException{"Unexpected reification type in s_exprify"}; return "";}
        }.visit(_reif_cond);

    string cmp = fmt::format("{}{}{}", 
        _vars_swapped ? "greater_than" : "less_than",
        _or_equal ? "_equal" : "",
        reif);

    if (reif.empty()) {
        print(s, "{} {} {} {}", name, cmp,
            model->names_and_ids_tracker().s_expr_name_of(_v1),
            model->names_and_ids_tracker().s_expr_name_of(_v2));
    }
    else {
        print(s, "{} {} {} {} {}", name, cmp, "Z",
            model->names_and_ids_tracker().s_expr_name_of(_v1),
            model->names_and_ids_tracker().s_expr_name_of(_v2));
    }
    

    return s.str();
}