#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/justify_not_in_range.hh>
#include <gcs/constraints/innards/reified_dispatcher.hh>
#include <gcs/exception.hh>
#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>

#include <util/overloaded.hh>

#include <sstream>
#include <variant>
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
    auto & inference, const ReasonLiterals & reason) -> PropagatorState
{
    auto val1 = state.optional_single_value(v1);
    if (val1) {
        inference.infer_equal(logger, v2, *val1, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v1 == *val1); return reason; }}, AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals});
        return PropagatorState::DisableUntilBacktrack;
    }

    auto val2 = state.optional_single_value(v2);
    if (val2) {
        inference.infer_equal(logger, v1, *val2, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v2 == *val2); return reason; }}, AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals});
        return PropagatorState::DisableUntilBacktrack;
    }

    if (state.domain_has_holes(v1) || state.domain_has_holes(v2)) {
        // Symmetric difference: remove from each side anything not present in
        // the other. Materialise both domains once and walk via merge —
        // O(intervals(v1) + intervals(v2) + |output|) instead of the
        // O(|domain| × intervals(other)) per-value membership scan.
        auto v1_set = state.copy_of_values(v1);
        auto v2_set = state.copy_of_values(v2);

        // Each contiguous removed interval is one ~[pruned in lo..hi] conclusion with
        // the matching reason `other not in [lo, hi]`. The conclusion is not RUP on
        // its own (a range literal asserts order atoms, never bits, so it cannot
        // cross the bit-sum equality), so two bound-lemmas carry the bounds across
        // first; each is RUP via the contradictory-binary-sums configuration. See
        // justify_not_in_range_across_equality. Views and constants take the
        // per-value path.
        auto both_simple = std::holds_alternative<SimpleIntegerVariableID>(IntegerVariableID{v1}) &&
            std::holds_alternative<SimpleIntegerVariableID>(IntegerVariableID{v2});

        auto bridge = [logger](const auto & pruned, const auto & other, Integer lo, Integer hi, const ReasonFunction & r) {
            // Plain equality pruned = other, so the flag forces other into the same [lo, hi].
            justify_not_in_range_across_equality(*logger, r,
                std::get<SimpleIntegerVariableID>(IntegerVariableID{pruned}), lo, hi,
                IntegerVariableID{other}, lo, hi);
        };

        auto prune = [&](const auto & pruned, const auto & other, const IntervalSet<Integer> & pruned_set, const IntervalSet<Integer> & other_set) {
            for (auto [lo, hi] : pruned_set.each_interval_minus(other_set)) {
                if (both_simple)
                    inference.infer_not_in_range(logger, pruned, lo, hi,
                        JustifyExplicitlyThenRUP{[=](const ReasonFunction & r) { bridge(pruned, other, lo, hi, r); }},
                        // Build afresh per call: the justification calls the reason once
                        // per bridge lemma plus once for the conclusion, so a mutable
                        // accumulating lambda would duplicate the element on each call.
                        ReasonFunction{[=, base = reason]() {
                            auto r = base;
                            r.emplace_back(not_in_range(IntegerVariableID{other}, lo, hi));
                            return r;
                        }},
                        AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals});
                else
                    for (Integer val = lo; val <= hi; ++val)
                        inference.infer_not_equal(logger, pruned, val, JustifyUsingRUP{},
                            ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(other != val); return reason; }}, AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals});
            }
        };

        prune(v1, v2, v1_set, v2_set);
        prune(v2, v1, v2_set, v1_set);
    }
    else {
        auto bounds1 = state.bounds(v1), bounds2 = state.bounds(v2);
        if (bounds1 != bounds2) {
            inference.infer_greater_than_or_equal(logger, v2, bounds1.first, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v1 >= bounds1.first); return reason; }}, AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals});
            inference.infer_greater_than_or_equal(logger, v1, bounds2.first, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v2 >= bounds2.first); return reason; }}, AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals});
            inference.infer_less_than(logger, v2, bounds1.second + 1_i, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v1 <= bounds1.second); return reason; }}, AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals});
            inference.infer_less_than(logger, v1, bounds2.second + 1_i, JustifyUsingRUP{}, ReasonFunction{[=, reason = reason]() mutable { reason.emplace_back(v2 <= bounds2.second); return reason; }}, AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals});
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
        ReasonLiterals reason{{v1 >= v1_bounds.first, v1 <= v1_bounds.second}};

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
            // cake_pb_cp: V1 = V2 split into le (V1 <= V2) and ge (V1 >= V2).
            model.add_labelled_constraint(as_string(_constraint_id), "le", "ge", "ReifiedEquals", "equals option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i);
        },
        [&](const reif::MustNotHold &) {
            // cake_pb_cp: V1 != V2 split into gt (V1 > V2) and lt (V1 < V2) on a
            // single per-constraint selector b[id][ne] (cake's `nev`): the flag
            // true selects the gt half, false the lt half.
            auto neflag = model.create_proof_flag(_constraint_id, "ne");
            model.add_labelled_constraint(as_string(_constraint_id), "gt", "ReifiedEquals", "not equals: greater half",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 1_i, HalfReifyOnConjunctionOf{{neflag}});
            model.add_labelled_constraint(as_string(_constraint_id), "lt", "ReifiedEquals", "not equals: less half",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= -1_i, HalfReifyOnConjunctionOf{{! neflag}});
        },
        [&](const reif::If & reif) {
            // cake_pb_cp's encode_equal (-if): the equality split le (V1 <= V2) and
            // ge (V1 >= V2), each half-reified on the condition. Labelled @c[id][le] /
            // @c[id][ge] to match cake's cencode_equal_1.
            model.add_labelled_constraint(as_string(_constraint_id), "le", "ge", "ReifiedEquals", "equals option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i, HalfReifyOnConjunctionOf{{reif.cond}});
        },
        [&](const reif::NotIf & reif) {
            // cake_pb_cp's reified not-equal (-if): selectors b[id][gt] / b[id][lt]
            // FULLY reified against the strict comparisons (both the [r] and [f] halves,
            // each labelled with the flag's own name), plus an at-least-one @c[id][al1]
            // over lt, gt and the NEGATED condition -- i.e. cond ⇒ (V1 < V2 ∨ V1 > V2).
            auto gtflag = model.create_proof_flag(_constraint_id, "gt");
            auto gt_name = model.names_and_ids_tracker().pb_file_string_for(gtflag);
            model.add_labelled_constraint(gt_name + "[r]",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 1_i, HalfReifyOnConjunctionOf{{gtflag}});
            model.add_labelled_constraint(gt_name + "[f]",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= 0_i, HalfReifyOnConjunctionOf{{! gtflag}});
            auto ltflag = model.create_proof_flag(_constraint_id, "lt");
            auto lt_name = model.names_and_ids_tracker().pb_file_string_for(ltflag);
            model.add_labelled_constraint(lt_name + "[r]",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= -1_i, HalfReifyOnConjunctionOf{{ltflag}});
            model.add_labelled_constraint(lt_name + "[f]",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 0_i, HalfReifyOnConjunctionOf{{! ltflag}});
            model.add_labelled_constraint(as_string(_constraint_id), "al1", "ReifiedEquals", "at least one differs",
                WPBSum{} + 1_i * ltflag + 1_i * gtflag + 1_i * ! reif.cond >= 1_i);
        },
        [&](const reif::Iff & reif) {
            // cake_pb_cp's encode_equal (-iff): the equality split le/ge half-reified on
            // the condition (@c[id][le] / @c[id][ge], cencode_equal_1); per-side selectors
            // b[id][gt] / b[id][lt] half-implying the strict comparisons (cake's gtv/ltv
            // via cvar_imply, each labelled with the flag's own name + [r]); and an
            // at-least-one @c[id][al1] tying lt, gt and the condition together.
            model.add_labelled_constraint(as_string(_constraint_id), "le", "ge", "ReifiedEquals", "equals option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i, HalfReifyOnConjunctionOf{{reif.cond}});

            auto gtflag = model.create_proof_flag(_constraint_id, "gt");
            model.add_labelled_constraint(model.names_and_ids_tracker().pb_file_string_for(gtflag) + "[r]",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 1_i, HalfReifyOnConjunctionOf{{gtflag}});
            auto ltflag = model.create_proof_flag(_constraint_id, "lt");
            model.add_labelled_constraint(model.names_and_ids_tracker().pb_file_string_for(ltflag) + "[r]",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= -1_i, HalfReifyOnConjunctionOf{{ltflag}});

            model.add_labelled_constraint(as_string(_constraint_id), "al1", "ReifiedEquals", "one of less than, equals, greater than",
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
            return enforce_equality(logger, v1, v2, state, inference, ReasonLiterals{cond});
        },
            v1, v2);
    };

    auto enforce_constraint_must_not_hold = [v1 = _v1, v2 = _v2](
                                                const State & state, auto & inference, ProofLogger * const logger,
                                                const Literal & cond) -> PropagatorState {
        auto value1 = state.optional_single_value(v1);
        if (value1) {
            inference.infer_not_equal(logger, v2, *value1, JustifyUsingRUP{},
                ReasonFunction{[=]() { return ReasonLiterals{{cond, v1 == *value1}}; }}, AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals});
            return PropagatorState::DisableUntilBacktrack;
        }
        auto value2 = state.optional_single_value(v2);
        if (value2) {
            inference.infer_not_equal(logger, v1, *value2, JustifyUsingRUP{},
                ReasonFunction{[=]() { return ReasonLiterals{{cond, v2 == *value2}}; }}, AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals});
            return PropagatorState::DisableUntilBacktrack;
        }
        return PropagatorState::Enable;
    };

    auto infer_cond_when_undecided = [v1 = _v1, v2 = _v2](
                                         const State & state, auto &, ProofLogger * const logger,
                                         const IntegerVariableCondition & cond) -> ReificationVerdict {
        // Aliased non-constant operands: equality definitely holds regardless of
        // domain. Returning MustHold here lets the dispatcher pin the cond
        // immediately at root, instead of waiting until search fixes v1 to a
        // value and the singleton check below fires.
        if (v1 == v2 && ! is_constant_variable(v1))
            return reification_verdict::MustHold{
                .justification = JustifyUsingRUP{},
                .reason = ReasonFunction{},
                .assertion_hint = AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals}};
        auto value1 = state.optional_single_value(v1);
        auto value2 = state.optional_single_value(v2);
        if (value1 && value2) {
            auto reason = ReasonFunction{[=]() { return ReasonLiterals{v1 == *value1, v2 == *value2}; }};
            if (*value1 == *value2)
                return reification_verdict::MustHold{.justification = JustifyUsingRUP{}, .reason = reason, .assertion_hint = AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals}};
            else
                return reification_verdict::MustNotHold{.justification = JustifyUsingRUP{}, .reason = reason, .assertion_hint = AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals}};
        }
        else if (value1) {
            if (! state.in_domain(v2, *value1))
                return reification_verdict::MustNotHold{
                    .justification = JustifyUsingRUP{},
                    .reason = ReasonFunction{[=]() { return ReasonLiterals{v1 == *value1, v2 != *value1}; }},
                    .assertion_hint = AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals}};
            return reification_verdict::StillUndecided{};
        }
        else if (value2) {
            if (! state.in_domain(v1, *value2))
                return reification_verdict::MustNotHold{
                    .justification = JustifyUsingRUP{},
                    .reason = ReasonFunction{[=]() { return ReasonLiterals{v2 == *value2, v1 != *value2}; }},
                    .assertion_hint = AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals}};
            return reification_verdict::StillUndecided{};
        }
        else {
            // not equals is forced if there's no overlap between domains
            if (! state.domains_intersect(v1, v2)) {
                auto [just, reason] = no_overlap_justification(state, logger, v1, v2, cond);
                return reification_verdict::MustNotHold{.justification = just, .reason = reason, .assertion_hint = AssertionAnnotation{.hint_name = AssertionHintName::ReifiedEquals}};
            }
            return reification_verdict::StillUndecided{};
        }
    };

    Triggers triggers;
    triggers.on_change = {_v1, _v2};
    install_reified_dispatcher(propagators, constraint_id(), _evaluated_cond, _cond, triggers,
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
    // Two constants that happen to be equal is a valid (if trivially
    // infeasible) model; only reject true variable aliasing.
    if (v1 == v2 && ! is_constant_variable(v1))
        throw InvalidProblemDefinitionException{"NotEquals: both operands are the same variable handle"};
}

NotEqualsIf::NotEqualsIf(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
    ReifiedEquals(v1, v2, reif::NotIf{cond}, true)
{
}

NotEqualsIff::NotEqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
    ReifiedEquals(v1, v2, reif::Iff{! cond}, true)
{
}

auto ReifiedEquals::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    string constraint_type = overloaded{
        [](const reif::MustHold &) -> string { return "equals"; },
        [](const reif::MustNotHold &) -> string { return "not_equals"; },
        [](const reif::If &) -> string { return "equals_if"; },
        [](const reif::NotIf &) -> string { return "not_equals_if"; },
        [&](const reif::Iff &) -> string {
            return _neq ? "not_equals_iff" : "equals_iff";
        }}.visit(_cond);

    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type)};
    if (auto cond = tracker.s_expr_term_of(_cond))
        terms.push_back(std::move(*cond));
    terms.push_back(tracker.s_expr_term_of(_v1));
    terms.push_back(tracker.s_expr_term_of(_v2));

    return SExpr::list(std::move(terms));
}

template auto gcs::innards::enforce_equality(ProofLogger * const logger, const IntegerVariableID & v1, const IntegerVariableID & v2, const State & state,
    SimpleInferenceTracker & inference, const ReasonLiterals & reason) -> PropagatorState;
template auto gcs::innards::enforce_equality(ProofLogger * const logger, const IntegerVariableID & v1, const IntegerVariableID & v2, const State & state,
    EagerProofLoggingInferenceTracker & inference, const ReasonLiterals & reason) -> PropagatorState;
