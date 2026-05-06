#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/reified_dispatcher.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <util/overloaded.hh>

#include <sstream>
#include <vector>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

auto gcs::innards::enforce_equality(ProofLogger * const logger, const auto & v1, const auto & v2, const State & state,
    auto & inference, const Reason & reason) -> PropagatorState
{
    auto val1 = state.optional_single_value(v1);
    if (val1) {
        inference.infer_equal(logger, v2, *val1, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v1 == *val1); return reason; }});
        return PropagatorState::DisableUntilBacktrack;
    }

    auto val2 = state.optional_single_value(v2);
    if (val2) {
        inference.infer_equal(logger, v1, *val2, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v2 == *val2); return reason; }});
        return PropagatorState::DisableUntilBacktrack;
    }

    if (state.domain_has_holes(v1) || state.domain_has_holes(v2)) {
        for (auto val : state.each_value_mutable(v1))
            if (! state.in_domain(v2, val))
                inference.infer_not_equal(logger, v1, val, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v2 != val); return reason; }});

        for (auto val : state.each_value_mutable(v2))
            if (! state.in_domain(v1, val))
                inference.infer_not_equal(logger, v2, val, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v1 != val); return reason; }});
    }
    else {
        auto bounds1 = state.bounds(v1), bounds2 = state.bounds(v2);
        if (bounds1 != bounds2) {
            inference.infer_greater_than_or_equal(logger, v2, bounds1.first, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v1 >= bounds1.first); return reason; }});
            inference.infer_greater_than_or_equal(logger, v1, bounds2.first, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v2 >= bounds2.first); return reason; }});
            inference.infer_less_than(logger, v2, bounds1.second + 1_i, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v1 < bounds1.second + 1_i); return reason; }});
            inference.infer_less_than(logger, v1, bounds2.second + 1_i, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v2 < bounds2.second + 1_i); return reason; }});
        }
    }

    return PropagatorState::Enable;
}

namespace
{
    auto no_overlap_justification(const State & state, ProofLogger * const logger,
        IntegerVariableID v1, IntegerVariableID v2, Literal cond) -> pair<JustifyExplicitlyThenRUP, ReasonFunction>
    {
        auto v1_bounds = state.bounds(v1);
        Reason reason{{v1 >= v1_bounds.first, v1 < v1_bounds.second + 1_i}};

        for (Integer val = v1_bounds.first; val <= v1_bounds.second; ++val)
            if (state.in_domain(v1, val))
                reason.emplace_back(v2 != val);
            else
                reason.emplace_back(v1 != val);

        auto justify = [&state = state, logger = logger, v1 = v1, v2 = v2, v1_bounds = v1_bounds, cond = cond](
                           const ReasonFunction &) {
            for (Integer val = v1_bounds.first; val <= v1_bounds.second; ++val)
                if (state.in_domain(v1, val))
                    logger->emit_rup_proof_line(WPBSum{} + 1_i * (v1 != val) + 1_i * (v2 == val) + 1_i * ! cond >= 1_i, ProofLevel::Temporary);
                else
                    logger->emit_rup_proof_line(WPBSum{} + 1_i * (v2 != val) + 1_i * (v1 == val) + 1_i * ! cond >= 1_i, ProofLevel::Temporary);
        };

        return pair{JustifyExplicitlyThenRUP{justify}, ReasonFunction{[=]() { return reason; }}};
    }
}

ReifiedEquals::ReifiedEquals(const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool neq) :
    _v1(v1),
    _v2(v2),
    _cond(cond),
    _neq(neq)
{
}

auto ReifiedEquals::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ReifiedEquals>(_v1, _v2, _cond);
}

auto ReifiedEquals::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto ReifiedEquals::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _evaluated_cond = test_reification_condition(initial_state, _cond);
    return true;
}

auto ReifiedEquals::define_proof_model(ProofModel & model) -> void
{
    overloaded{
        [&](const reif::MustHold &) {
            model.add_constraint("ReifiedEquals", "equals option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i);
        },
        [&](const reif::MustNotHold &) {
            auto gtflag = model.create_proof_flag("gt");
            model.add_constraint("ReifiedEquals", "greater option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 1_i, HalfReifyOnConjunctionOf{{gtflag}});
            model.add_constraint("ReifiedEquals", "less option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= -1_i, HalfReifyOnConjunctionOf{{! gtflag}});
        },
        [&](const reif::If & reif) {
            model.add_constraint("ReifiedEquals", "equals option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i, HalfReifyOnConjunctionOf{{reif.cond}});
        },
        [&](const reif::NotIf & reif) {
            auto gtflag = model.create_proof_flag("gt");
            model.add_constraint("ReifiedEquals", "greater option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 1_i, HalfReifyOnConjunctionOf{{reif.cond, gtflag}});
            model.add_constraint("ReifiedEquals", "less option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= -1_i, HalfReifyOnConjunctionOf{{reif.cond, ! gtflag}});
        },
        [&](const reif::Iff & reif) {
            // condition unknown, the condition implies it is neither greater nor less
            model.add_constraint("ReifiedEquals", "equals option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i, HalfReifyOnConjunctionOf{{reif.cond}});

            auto gtflag = model.create_proof_flag("gt");
            model.add_constraint("ReifiedEquals", "greater option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 1_i, HalfReifyOnConjunctionOf{{gtflag}});
            auto ltflag = model.create_proof_flag("lt");
            model.add_constraint("ReifiedEquals", "less option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= -1_i, HalfReifyOnConjunctionOf{{ltflag}});

            // lt + eq + gt >= 1
            model.add_constraint("ReifiedEquals", "one of less than, equals, greater than",
                WPBSum{} + 1_i * ltflag + 1_i * gtflag + 1_i * reif.cond >= 1_i);
        }}
        .visit(_cond);
}

auto ReifiedEquals::install_propagators(Propagators & propagators) -> void
{
    auto enforce_constraint_must_hold = [v1 = _v1, v2 = _v2](
                                            const State & state, auto & inference, ProofLogger * const logger,
                                            const Literal & cond) -> PropagatorState {
        return visit([&](auto & v1, auto & v2) {
            return enforce_equality(logger, v1, v2, state, inference, Reason{cond});
        },
            v1, v2);
    };

    auto enforce_constraint_must_not_hold = [v1 = _v1, v2 = _v2](
                                                const State & state, auto & inference, ProofLogger * const logger,
                                                const Literal & cond) -> PropagatorState {
        auto value1 = state.optional_single_value(v1);
        if (value1) {
            inference.infer_not_equal(logger, v2, *value1, JustifyUsingRUP{},
                ReasonFunction{[=]() { return Reason{{cond, v1 == *value1}}; }});
            return PropagatorState::DisableUntilBacktrack;
        }
        auto value2 = state.optional_single_value(v2);
        if (value2) {
            inference.infer_not_equal(logger, v1, *value2, JustifyUsingRUP{},
                ReasonFunction{[=]() { return Reason{{cond, v2 == *value2}}; }});
            return PropagatorState::DisableUntilBacktrack;
        }
        return PropagatorState::Enable;
    };

    auto infer_cond_when_undecided = [v1 = _v1, v2 = _v2](
                                         const State & state, auto &, ProofLogger * const logger,
                                         const IntegerVariableCondition & cond) -> ReificationVerdict {
        auto value1 = state.optional_single_value(v1);
        auto value2 = state.optional_single_value(v2);
        if (value1 && value2) {
            auto reason = ReasonFunction{[=]() { return Reason{v1 == *value1, v2 == *value2}; }};
            if (*value1 == *value2)
                return reification_verdict::MustHold{.justification = JustifyUsingRUP{}, .reason = reason};
            else
                return reification_verdict::MustNotHold{.justification = JustifyUsingRUP{}, .reason = reason};
        }
        else if (value1) {
            if (! state.in_domain(v2, *value1))
                return reification_verdict::MustNotHold{
                    .justification = JustifyUsingRUP{},
                    .reason = ReasonFunction{[=]() { return Reason{v1 == *value1, v2 != *value1}; }}};
            return reification_verdict::StillUndecided{};
        }
        else if (value2) {
            if (! state.in_domain(v1, *value2))
                return reification_verdict::MustNotHold{
                    .justification = JustifyUsingRUP{},
                    .reason = ReasonFunction{[=]() { return Reason{v2 == *value2, v1 != *value2}; }}};
            return reification_verdict::StillUndecided{};
        }
        else {
            // not equals is forced if there's no overlap between domains
            bool overlap = false;
            for (auto val : state.each_value_immutable(v1))
                if (state.in_domain(v2, val)) {
                    overlap = true;
                    break;
                }

            if (! overlap) {
                auto [just, reason] = no_overlap_justification(state, logger, v1, v2, cond);
                return reification_verdict::MustNotHold{.justification = just, .reason = reason};
            }
            return reification_verdict::StillUndecided{};
        }
    };

    Triggers triggers;
    triggers.on_change = {_v1, _v2};
    install_reified_dispatcher(propagators, _evaluated_cond, _cond, triggers,
        std::move(enforce_constraint_must_hold),
        std::move(enforce_constraint_must_not_hold),
        std::move(infer_cond_when_undecided));
}

Equals::Equals(const IntegerVariableID v1, const IntegerVariableID v2) :
    ReifiedEquals(v1, v2, reif::MustHold{})
{
}

EqualsIf::EqualsIf(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
    ReifiedEquals(v1, v2, reif::If{cond})
{
}

EqualsIff::EqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
    ReifiedEquals(v1, v2, reif::Iff{cond})
{
}

NotEquals::NotEquals(const IntegerVariableID v1, const IntegerVariableID v2) :
    ReifiedEquals(v1, v2, reif::MustNotHold{}, true)
{
}

NotEqualsIf::NotEqualsIf(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
    ReifiedEquals(v1, v2, reif::NotIf{cond}, true)
{
}

NotEqualsIff::NotEqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
    ReifiedEquals(v1, v2, reif::Iff{! cond}, true)
{
}

auto ReifiedEquals::s_exprify(const string & name, const innards::ProofModel * const model) const -> string
{
    stringstream s;

    string constraint_type = overloaded{
        [](const reif::MustHold &) -> string { return "equals"; },
        [](const reif::MustNotHold &) -> string { return "not_equals"; },
        [](const reif::If &) -> string { return "equals_if"; },
        [](const reif::NotIf &) -> string { return "not_equals_if"; },
        [&](const reif::Iff &) -> string {
            return _neq ? "not_equals_iff" : "equals_iff";
        }}.visit(_cond);

    print(s, "{} {}", name, constraint_type);
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_cond));
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_v1));
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_v2));

    return s.str();
}

template auto gcs::innards::enforce_equality(ProofLogger * const logger, const IntegerVariableID & v1, const IntegerVariableID & v2, const State & state,
    SimpleInferenceTracker & inference, const Reason & reason) -> PropagatorState;
template auto gcs::innards::enforce_equality(ProofLogger * const logger, const IntegerVariableID & v1, const IntegerVariableID & v2, const State & state,
    EagerProofLoggingInferenceTracker & inference, const Reason & reason) -> PropagatorState;
