#include <gcs/constraints/equals/equals.hh>
#include <gcs/constraints/equals/hints.hh>
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

namespace gcs::innards::hints
{
    auto emit_justification(ProofLogger & logger, const EqualsNoOverlap & w, const ReasonLiterals &) -> void
    {
        for (Integer val = w.v1_bounds.first; val <= w.v1_bounds.second; ++val)
            if (w.state->in_domain(w.v1, val))
                logger.emit_rup_proof_line(WPBSum{} + 1_i * (w.v1 != val) + 1_i * (w.v2 == val) + 1_i * ! w.cond >= 1_i, ProofLevel::Temporary);
            else
                logger.emit_rup_proof_line(WPBSum{} + 1_i * (w.v2 != val) + 1_i * (w.v1 == val) + 1_i * ! w.cond >= 1_i, ProofLevel::Temporary);
    }
}

auto gcs::innards::enforce_equality(ProofLogger * const logger, const auto & v1, const auto & v2, const State & state, auto & inference,
    const ReasonLiterals & reason, const ConstraintID & owner) -> PropagatorState
{
    auto val1 = state.optional_single_value(v1);
    if (val1) {
        inference.infer_equal(logger, v2, *val1, JustifyUsingRUP{hints::Equals{owner}},
            ExplicitReason{//
                [&] {
                    auto r = reason;
                    r.emplace_back(v1 == *val1);
                    return r;
                }()});
        return PropagatorState::DisableUntilBacktrack;
    }

    auto val2 = state.optional_single_value(v2);
    if (val2) {
        inference.infer_equal(logger, v1, *val2, JustifyUsingRUP{hints::Equals{owner}},
            ExplicitReason{//
                [&] {
                    auto r = reason;
                    r.emplace_back(v2 == *val2);
                    return r;
                }()});
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

        auto bridge = [logger](const auto & pruned, const auto & other, Integer lo, Integer hi, const ReasonLiterals & r) {
            // Plain equality pruned = other, so the flag forces other into the same [lo, hi].
            justify_not_in_range_across_equality(
                *logger, r, std::get<SimpleIntegerVariableID>(IntegerVariableID{pruned}), lo, hi, IntegerVariableID{other}, lo, hi);
        };

        auto prune = [&](const auto & pruned, const auto & other, const IntervalSet<Integer> & pruned_set, const IntervalSet<Integer> & other_set) {
            for (auto [lo, hi] : pruned_set.each_interval_minus(other_set)) {
                if (both_simple) {
                    // ExplicitReason holds an immutable snapshot (the base reason plus
                    // the excluded interval), so the justification — which materialises
                    // it once per bridge lemma plus once for the conclusion — gets a
                    // fresh copy each time rather than an accumulating element.
                    ReasonLiterals not_in_range_reason = reason;
                    not_in_range_reason.emplace_back(not_in_range(IntegerVariableID{other}, lo, hi));
                    inference.infer_not_in_range(logger, pruned, lo, hi,
                        JustifyExplicitly{[=](const ReasonLiterals & r) { bridge(pruned, other, lo, hi, r); }, ThenRUP::Yes, hints::Equals{owner}},
                        ExplicitReason{std::move(not_in_range_reason)});
                }
                else
                    for (Integer val = lo; val <= hi; ++val)
                        inference.infer_not_equal(logger, pruned, val, JustifyUsingRUP{hints::Equals{owner}},
                            ExplicitReason{//
                                [&] {
                                    auto r = reason;
                                    r.emplace_back(other != val);
                                    return r;
                                }()});
            }
        };

        prune(v1, v2, v1_set, v2_set);
        prune(v2, v1, v2_set, v1_set);
    }
    else {
        auto bounds1 = state.bounds(v1), bounds2 = state.bounds(v2);
        if (bounds1 != bounds2) {
            inference.infer_greater_than_or_equal(logger, v2, bounds1.first, JustifyUsingRUP{hints::Equals{owner}},
                ExplicitReason{//
                    [&] {
                        auto r = reason;
                        r.emplace_back(v1 >= bounds1.first);
                        return r;
                    }()});
            inference.infer_greater_than_or_equal(logger, v1, bounds2.first, JustifyUsingRUP{hints::Equals{owner}},
                ExplicitReason{//
                    [&] {
                        auto r = reason;
                        r.emplace_back(v2 >= bounds2.first);
                        return r;
                    }()});
            inference.infer_less_than(logger, v2, bounds1.second + 1_i, JustifyUsingRUP{hints::Equals{owner}},
                ExplicitReason{//
                    [&] {
                        auto r = reason;
                        r.emplace_back(v1 <= bounds1.second);
                        return r;
                    }()});
            inference.infer_less_than(logger, v1, bounds2.second + 1_i, JustifyUsingRUP{hints::Equals{owner}},
                ExplicitReason{//
                    [&] {
                        auto r = reason;
                        r.emplace_back(v2 <= bounds2.second);
                        return r;
                    }()});
        }
    }

    return PropagatorState::Enable;
}

namespace
{
    auto no_overlap_justification(const State & state, ProofLogger * const, IntegerVariableID v1, IntegerVariableID v2, Literal cond,
        const ConstraintID & owner) -> pair<hints::EqualsNoOverlap, Reason>
    {
        auto v1_bounds = state.bounds(v1);
        ReasonLiterals reason{{v1 >= v1_bounds.first, v1 <= v1_bounds.second}};

        for (Integer val = v1_bounds.first; val <= v1_bounds.second; ++val)
            if (state.in_domain(v1, val))
                reason.emplace_back(v2 != val);
            else
                reason.emplace_back(v1 != val);

        return pair{hints::EqualsNoOverlap{{owner}, &state, v1, v2, v1_bounds, cond}, ExplicitReason{reason}};
    }

    // equals's reified verdicts are either a plain RUP (the singleton / forced
    // cases) or the no-overlap witness; a variant of the two, visited inside infer.
    using EqualsJustification = std::variant<JustifyUsingRUP<hints::Equals>, JustifyExplicitly<hints::EqualsNoOverlap>>;
}

ReifiedEquals::ReifiedEquals(const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool neq) :
    _v1(v1), _v2(v2), _cond(cond), _neq(neq)
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
            model.add_labelled_constraint(
                as_string(_constraint_id), "le", "ge", "ReifiedEquals", "equals option", WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i);
        }, //
        [&](const reif::MustNotHold &) {
            // cake_pb_cp: V1 != V2 split into gt (V1 > V2) and lt (V1 < V2) on a
            // single per-constraint selector b[id][ne] (cake's `nev`): the flag
            // true selects the gt half, false the lt half.
            auto neflag = model.create_proof_flag(_constraint_id, "ne");
            model.add_labelled_constraint(as_string(_constraint_id), "gt", "ReifiedEquals", "not equals: greater half",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 1_i, HalfReifyOnConjunctionOf{{neflag}});
            model.add_labelled_constraint(as_string(_constraint_id), "lt", "ReifiedEquals", "not equals: less half",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= -1_i, HalfReifyOnConjunctionOf{{! neflag}});
        }, //
        [&](const reif::If & reif) {
            // cake_pb_cp's encode_equal (-if): the equality split le (V1 <= V2) and
            // ge (V1 >= V2), each half-reified on the condition. Labelled @c[id][le] /
            // @c[id][ge] to match cake's cencode_equal_1.
            model.add_labelled_constraint(as_string(_constraint_id), "le", "ge", "ReifiedEquals", "equals option",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i, HalfReifyOnConjunctionOf{{reif.cond}});
        }, //
        [&](const reif::NotIf & reif) {
            // cake_pb_cp's reified not-equal (-if): selectors b[id][gt] / b[id][lt]
            // FULLY reified against the strict comparisons (both the [r] and [f] halves,
            // each labelled with the flag's own name), plus an at-least-one @c[id][al1]
            // over lt, gt and the NEGATED condition -- i.e. cond ⇒ (V1 < V2 ∨ V1 > V2).
            auto gtflag = model.create_proof_flag(_constraint_id, "gt");
            auto gt_name = model.names_and_ids_tracker().pb_file_string_for(gtflag);
            model.add_labelled_constraint(gt_name + "[r]", WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 1_i, HalfReifyOnConjunctionOf{{gtflag}});
            model.add_labelled_constraint(gt_name + "[f]", WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= 0_i, HalfReifyOnConjunctionOf{{! gtflag}});
            auto ltflag = model.create_proof_flag(_constraint_id, "lt");
            auto lt_name = model.names_and_ids_tracker().pb_file_string_for(ltflag);
            model.add_labelled_constraint(lt_name + "[r]", WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= -1_i, HalfReifyOnConjunctionOf{{ltflag}});
            model.add_labelled_constraint(lt_name + "[f]", WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 0_i, HalfReifyOnConjunctionOf{{! ltflag}});
            model.add_labelled_constraint(as_string(_constraint_id), "al1", "ReifiedEquals", "at least one differs",
                WPBSum{} + 1_i * ltflag + 1_i * gtflag + 1_i * ! reif.cond >= 1_i);
        }, //
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
        } //
    }
        .visit(_cond);
}

auto ReifiedEquals::install_propagators(Propagators & propagators) -> void
{
    auto enforce_constraint_must_hold = [v1 = _v1, v2 = _v2, owner = constraint_id()](const State & state, auto & inference,
                                            ProofLogger * const logger, const Literal & cond) -> PropagatorState {
        return visit([&](auto & v1, auto & v2) { return enforce_equality(logger, v1, v2, state, inference, ReasonLiterals{cond}, owner); }, v1, v2);
    };

    auto v1_scope = std::make_shared<const std::vector<IntegerVariableID>>(std::vector<IntegerVariableID>{_v1});
    auto v2_scope = std::make_shared<const std::vector<IntegerVariableID>>(std::vector<IntegerVariableID>{_v2});
    auto v1v2_scope = std::make_shared<const std::vector<IntegerVariableID>>(std::vector<IntegerVariableID>{_v1, _v2});
    auto enforce_constraint_must_not_hold = [v1 = _v1, v2 = _v2, v1_scope, v2_scope, owner = constraint_id()](const State & state, auto & inference,
                                                ProofLogger * const logger, const Literal & cond) -> PropagatorState {
        auto value1 = state.optional_single_value(v1);
        if (value1) {
            if (! inference.infer_not_equal_or_stop(logger, v2, *value1, JustifyUsingRUP{hints::Equals{owner}},
                    inference.want_reasons() ? concat(singleton_reason(cond), ExactSingleValue{ReasonVars{v1_scope.get()}}) : Reason{}))
                return PropagatorState::Enable; // contradiction: loop sees tracker.contradicted()
            return PropagatorState::DisableUntilBacktrack;
        }
        auto value2 = state.optional_single_value(v2);
        if (value2) {
            if (! inference.infer_not_equal_or_stop(logger, v1, *value2, JustifyUsingRUP{hints::Equals{owner}},
                    inference.want_reasons() ? concat(singleton_reason(cond), ExactSingleValue{ReasonVars{v2_scope.get()}}) : Reason{}))
                return PropagatorState::Enable; // contradiction: loop sees tracker.contradicted()
            return PropagatorState::DisableUntilBacktrack;
        }
        return PropagatorState::Enable;
    };

    auto infer_cond_when_undecided = [v1 = _v1, v2 = _v2, v1v2_scope, owner = constraint_id()](const State & state, auto &,
                                         ProofLogger * const logger,
                                         const IntegerVariableCondition & cond) -> ReificationVerdictFor<EqualsJustification> {
        // Aliased non-constant operands: equality definitely holds regardless of
        // domain. Returning MustHold here lets the dispatcher pin the cond
        // immediately at root, instead of waiting until search fixes v1 to a
        // value and the singleton check below fires.
        if (v1 == v2 && ! is_constant_variable(v1))
            return reification_verdict::MustHold<EqualsJustification>{
                .justification = JustifyUsingRUP{hints::Equals{owner}}, //
                .reason = NoReason{}                                    //
            };
        auto value1 = state.optional_single_value(v1);
        auto value2 = state.optional_single_value(v2);
        if (value1 && value2) {
            auto reason = Reason{ExactSingleValue{ReasonVars{v1v2_scope.get()}}};
            if (*value1 == *value2)
                return reification_verdict::MustHold<EqualsJustification>{
                    .justification = JustifyUsingRUP{hints::Equals{owner}}, //
                    .reason = reason                                        //
                };
            else
                return reification_verdict::MustNotHold<EqualsJustification>{
                    .justification = JustifyUsingRUP{hints::Equals{owner}}, //
                    .reason = reason                                        //
                };
        }
        else if (value1) {
            if (! state.in_domain(v2, *value1))
                return reification_verdict::MustNotHold<EqualsJustification>{
                    .justification = JustifyUsingRUP{hints::Equals{owner}},                //
                    .reason = ExplicitReason{ReasonLiterals{v1 == *value1, v2 != *value1}} //
                };
            return reification_verdict::StillUndecided{};
        }
        else if (value2) {
            if (! state.in_domain(v1, *value2))
                return reification_verdict::MustNotHold<EqualsJustification>{
                    .justification = JustifyUsingRUP{hints::Equals{owner}},                //
                    .reason = ExplicitReason{ReasonLiterals{v2 == *value2, v1 != *value2}} //
                };
            return reification_verdict::StillUndecided{};
        }
        else {
            // not equals is forced if there's no overlap between domains
            if (! state.domains_intersect(v1, v2)) {
                auto [no_overlap, reason] = no_overlap_justification(state, logger, v1, v2, cond, owner);
                return reification_verdict::MustNotHold<EqualsJustification>{
                    .justification = JustifyExplicitly{no_overlap, ThenRUP::Yes}, //
                    .reason = reason                                              //
                };
            }
            return reification_verdict::StillUndecided{};
        }
    };

    Triggers triggers;
    triggers.on_change = {_v1, _v2};
    install_reified_dispatcher(propagators, constraint_id(), _evaluated_cond, _cond, triggers, std::move(enforce_constraint_must_hold),
        std::move(enforce_constraint_must_not_hold), std::move(infer_cond_when_undecided));
}

Equals::Equals(const IntegerVariableID v1, const IntegerVariableID v2) : ReifiedEquals(v1, v2, reif::MustHold{})
{
}

EqualsIf::EqualsIf(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) : ReifiedEquals(v1, v2, reif::If{cond})
{
}

EqualsIff::EqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) : ReifiedEquals(v1, v2, reif::Iff{cond})
{
}

NotEquals::NotEquals(const IntegerVariableID v1, const IntegerVariableID v2) : ReifiedEquals(v1, v2, reif::MustNotHold{}, true)
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
        [](const reif::MustHold &) -> string { return "equals"; },                          //
        [](const reif::MustNotHold &) -> string { return "not_equals"; },                   //
        [](const reif::If &) -> string { return "equals_if"; },                             //
        [](const reif::NotIf &) -> string { return "not_equals_if"; },                      //
        [&](const reif::Iff &) -> string { return _neq ? "not_equals_iff" : "equals_iff"; } //
    }
                                 .visit(_cond);

    // A not-equals iff stores the negated condition (equality holds iff NOT the
    // user's condition), but the not_equals_iff keyword already carries the
    // negation: cake reads (r not_equals_iff (cond) v1 v2) as cond <=> v1 != v2.
    // Emit the user's original condition, not the stored one, or the two
    // negations cancel into the opposite constraint.
    auto cond_to_write =
        _neq && std::holds_alternative<reif::Iff>(_cond) ? ReificationCondition{reif::Iff{! std::get<reif::Iff>(_cond).cond}} : _cond;
    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type)};
    if (auto cond = tracker.s_expr_term_of(cond_to_write))
        terms.push_back(std::move(*cond));
    terms.push_back(tracker.s_expr_term_of(_v1));
    terms.push_back(tracker.s_expr_term_of(_v2));

    return SExpr::list(std::move(terms));
}

template auto gcs::innards::enforce_equality(ProofLogger * const logger, const IntegerVariableID & v1, const IntegerVariableID & v2,
    const State & state, SimpleInferenceTracker & inference, const ReasonLiterals & reason, const ConstraintID & owner) -> PropagatorState;
template auto gcs::innards::enforce_equality(ProofLogger * const logger, const IntegerVariableID & v1, const IntegerVariableID & v2,
    const State & state, EagerProofLoggingInferenceTracker & inference, const ReasonLiterals & reason, const ConstraintID & owner) -> PropagatorState;
