#include <gcs/constraints/equals/equals.hh>
#include <gcs/constraints/equals/hints.hh>
#include <gcs/constraints/innards/equals_mutations.hh>
#include <gcs/constraints/innards/justify_not_in_range.hh>
#include <gcs/constraints/innards/reified_dispatcher.hh>
#include <gcs/exception.hh>
#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/large_domain_guard.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/interval_set.hh>

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

namespace
{
    // One move of the no-overlap walk. The walk is the certificate that two
    // domains are disjoint, stated over *runs* rather than values: see
    // walk_no_overlap below for what it maintains and why these are the moves.
    enum class NoOverlapStep
    {
        AnchorV1Lower,    ///< the walk starts at v1's lower bound: `v1 >= lo`.
        JumpToV2Lower,    ///< `v2 >= lo`, so under cond v1 is there too. lo == hi.
        SkipV1Hole,       ///< v1 has no value in [lo, hi], so it is already past hi.
        SkipV2Hole,       ///< v2 has no value in [lo, hi], so under cond neither has v1.
        StopAboveV1Upper, ///< `v1 <= lo` and the walk has reached hi > lo: contradiction.
        StopAboveV2Upper  ///< `v2 <= lo` and the walk has reached hi > lo: contradiction, under cond.
    };

    // Walk two disjoint domains, reporting a certificate of their disjointness
    // whose length is the number of runs it takes to say it, not the number of
    // values the domains span.
    //
    // The walk carries one invariant up the number line: at each point p, the
    // facts reported so far (together with the reification condition, which
    // makes the two operands equal) force `v1 >= p`. It starts at v1's lower
    // bound, and each move pushes p past one maximal run of values v1 cannot
    // take -- either because v1 itself has nothing there, or because *v2* has
    // nothing there and under cond v1 must be wherever v2 is. p is strictly
    // increasing, so the walk stops after at most one move per interval of
    // either domain, and it stops by running p off the top of one of the two
    // domains, which is the contradiction the conclusion needs.
    //
    // Only the reason builder walks here, turning each move into a literal.
    // emit_justification does not: it reads the same walk back out of those
    // literals instead (#870), because the lemmas' whole job is to let unit
    // propagation see that reason's literals through, and taking the walk from
    // the reason is what makes the two certain to be reporting the same one.
    //
    // \p d1 and \p d2 must be non-empty and disjoint, which is exactly the
    // condition the rule fires under.
    template <typename Step_>
    auto walk_no_overlap(const IntervalSet<Integer> & d1, const IntervalSet<Integer> & d2, Step_ && step) -> void
    {
        vector<pair<Integer, Integer>> i1, i2;
        for (const auto & i : d1.each_interval())
            i1.push_back(i);
        for (const auto & i : d2.each_interval())
            i2.push_back(i);
        if (i1.empty() || i2.empty())
            throw UnexpectedException{"equals no-overlap walk over an empty domain"};

        auto [lb1, ub1] = pair{i1.front().first, i1.back().second};
        auto [lb2, ub2] = pair{i2.front().first, i2.back().second};

        // Establish `v1 >= p` for the first time. If v2 starts above v1 does,
        // v2's own lower bound gets us there and v1's is never mentioned --
        // which is what makes the bounds-disjoint case a two-literal reason.
        auto p = lb1;
        if (p < lb2) {
            step(NoOverlapStep::JumpToV2Lower, lb2, lb2);
            p = lb2;
        }
        else
            step(NoOverlapStep::AnchorV1Lower, lb1, lb1);

        // The cursors only ever move forwards, because p does; each keeps the
        // first interval of its domain that has not already been passed.
        std::size_t j1 = 0, j2 = 0;
        while (true) {
            if (p > ub1) {
                step(NoOverlapStep::StopAboveV1Upper, ub1, p);
                return;
            }
            if (p > ub2) {
                step(NoOverlapStep::StopAboveV2Upper, ub2, p);
                return;
            }

            // p <= ub1 and p <= ub2, so neither search runs off the end.
            while (i1[j1].second < p)
                ++j1;
            while (i2[j2].second < p)
                ++j2;

            if (p < i1[j1].first) {
                // p is outside v1. It may be outside v2 as well, in which case
                // the v2-free run from here could be the longer of the two and
                // taking it would end the walk in fewer moves. Take v1's anyway:
                // its move costs no lemmas, v2's costs two, and the choice only
                // ever changes the move count by a constant factor -- the bound
                // is one move per interval of either domain either way.
                auto hi = i1[j1].first - 1_i;
                step(NoOverlapStep::SkipV1Hole, p, hi);
                p = hi + 1_i;
            }
            else {
                // p is a value of v1, so disjointness says it is not one of v2,
                // and v2's next interval starts strictly above it.
                if (i2[j2].first <= p)
                    throw UnexpectedException{"equals no-overlap walk over domains that do overlap"};
                auto hi = i2[j2].first - 1_i;
                step(NoOverlapStep::SkipV2Hole, p, hi);
                p = hi + 1_i;
            }
        }
    }

}

namespace gcs::innards::hints
{
    auto emit_justification(ProofLogger & logger, const EqualsNoOverlap & w, const ReasonLiterals & reason) -> void
    {
        // Two lemma shapes, each carrying one bound across the reified equality.
        // The cond-guarded halves of the model constraint are `cond -> v1 <= v2`
        // and `cond -> v1 >= v2`, so each lemma's negation supplies a pair of
        // opposing bounds against one of them: the Theorem 2.9 configuration
        // that makes it RUP, exactly as in justify_not_in_range_across_equality
        // (which cannot be reused directly here only because these halves are
        // reified, so the lemmas carry the extra `! cond`).
        //
        // Testing only, and never on by default: `omit` emits no lemmas at all,
        // and `selector` states each of them under cond rather than ! cond. See
        // EqualsProofMutation.
        auto omit = std::holds_alternative<equals_proof_mutation::OmitNoOverlapLemmas>(w.mutation);
        auto selector = std::holds_alternative<equals_proof_mutation::FlipNoOverlapSelector>(w.mutation) ? Literal{w.cond} : Literal{! w.cond};

        auto v2_lower_reaches_v1 = [&](Integer k) {
            if (! omit)
                logger.emit_rup_proof_line(WPBSum{} + 1_i * selector + 1_i * (w.v2 < k) + 1_i * (w.v1 >= k) >= 1_i, ProofLevel::Temporary);
        };
        auto v1_lower_reaches_v2 = [&](Integer k) {
            if (! omit)
                logger.emit_rup_proof_line(WPBSum{} + 1_i * selector + 1_i * (w.v1 < k) + 1_i * (w.v2 >= k) >= 1_i, ProofLevel::Temporary);
        };

        // The walk is re-read out of the reason, not out of the domains. Both
        // are the same walk when nothing has moved, but a justification does not
        // run at the moment its inference was decided: by the time it does,
        // earlier pushes in the same propagation have landed, and a domain read
        // here can be narrower than the one the reason was built from -- at
        // which point the lemmas stop lining up with the literals they exist to
        // let unit propagation see through, and the conclusion's RUP check
        // fails. Reading the reason cannot go stale, because the reason is what
        // the conclusion is asserted under. This rule was the family's only
        // justification that touched state at all (issue #870).
        //
        // It is also the reconstructibility claim, exercised: the family
        // document says an external justifier can rebuild this derivation from
        // the assertion alone, and everything below is read from literals such a
        // justifier is handed too.
        //
        // What each move owes the conclusion's RUP check, given that the check
        // has cond and the reason's literals as units and is carrying `v1 >= p`:
        //
        //   `v1 >= lo`          the anchor; the reason literal is the fact.
        //   `v2 >= lo`          the same start reached through v2; one lemma
        //                       turns it into `v1 >= lo`.
        //   `~[v1 in lo..hi]`   nothing: that and `v1 >= lo` meet in the range
        //                       literal's own reverse reification, which gives
        //                       `v1 >= hi + 1`.
        //   `~[v2 in lo..hi]`   `v1 >= lo` crosses to `v2 >= lo`, that and the
        //                       literal give `v2 >= hi + 1` through v2's reverse
        //                       reification, and that crosses back.
        //   `v1 <= lo`          nothing: `v1 >= p` and it are opposite ends of
        //                       v1's own order chain.
        //   `v2 <= lo`          `v1 >= p` crosses to `v2 >= p`, against it.
        if (reason.empty())
            throw UnexpectedException{"equals no-overlap witness has no reason to re-walk"};

        // A reason literal is a ProofLiteralOrFlag in general; every literal this
        // witness's reason holds is a plain condition on one of the two operands.
        auto as_condition = [](const ProofLiteralOrFlag & literal) -> const IntegerVariableCondition * {
            if (const auto * proof_literal = std::get_if<ProofLiteral>(&literal))
                if (const auto * plain = std::get_if<Literal>(proof_literal))
                    return std::get_if<IntegerVariableCondition>(plain);
            return nullptr;
        };

        auto p = optional<Integer>{};
        for (std::size_t i = 0; i < reason.size();) {
            const auto * cond = as_condition(reason[i]);
            if (! cond || (cond->var != w.v1 && cond->var != w.v2))
                throw UnexpectedException{"equals no-overlap witness cannot re-walk its own reason"};
            auto on_v2 = (cond->var == w.v2);

            switch (cond->op) {
                using enum VariableConditionOperator;
            case GreaterEqual:
                if (on_v2)
                    v2_lower_reaches_v1(cond->value);
                p = cond->value;
                ++i;
                break;

            case NotEqual:
            case NotInRange: {
                // One maximal run of values that operand cannot take, and the
                // walk's position steps past it. A run is one range literal --
                // unless the operand is a view, which has none, and is then
                // spelled value by value (#882). So consecutive single-value
                // literals on the same operand are one run, and cost the two
                // lemmas a range literal would rather than two per value.
                auto lo = cond->value;
                auto hi = (cond->op == NotInRange ? cond->upper_value : cond->value);
                for (++i; cond->op == NotEqual && i < reason.size(); ++i) {
                    const auto * next = as_condition(reason[i]);
                    if (! next || next->op != NotEqual || next->var != cond->var || next->value != hi + 1_i)
                        break;
                    hi = next->value;
                }

                if (on_v2) {
                    v1_lower_reaches_v2(lo);
                    v2_lower_reaches_v1(hi + 1_i);
                }
                p = hi + 1_i;
            } break;

            case Less:
                if (on_v2) {
                    if (! p)
                        throw UnexpectedException{"equals no-overlap witness reached its stop before its anchor"};
                    v1_lower_reaches_v2(*p);
                }
                ++i;
                break;

            default: throw UnexpectedException{"equals no-overlap witness cannot re-walk a reason literal of this shape"};
            }
        }
    }
}

auto gcs::innards::enforce_equality(ProofLogger * const logger, const auto & v1, const auto & v2, const State & state, auto & inference,
    const ReasonLiterals & reason, const ConstraintID & owner, EqualsProofMutation mutation) -> PropagatorState
{
    // Testing only, and never on by default: see EqualsProofMutation.
    auto drop_fixed_operand_reason = std::holds_alternative<equals_proof_mutation::DropFixedOperandReason>(mutation);

    auto val1 = state.optional_single_value(v1);
    if (val1) {
        inference.infer_equal(logger, v2, *val1, JustifyUsingRUP{hints::Equals{owner}},
            ExplicitReason{//
                [&] {
                    auto r = reason;
                    if (! drop_fixed_operand_reason)
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
                    if (! drop_fixed_operand_reason)
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
        //
        // Hence the not_in_range subhint rather than the family's base hint: at
        // AssertionLevel::Inferences the lemmas are not written, and a justifier
        // reading only the annotation would otherwise see this three-line
        // derivation and a one-line RUP pruning wearing the same wire form
        // (issue #866). The per-value fallback below is a genuine one-line RUP,
        // so it keeps the base hint.
        auto both_simple = std::holds_alternative<SimpleIntegerVariableID>(IntegerVariableID{v1}) &&
            std::holds_alternative<SimpleIntegerVariableID>(IntegerVariableID{v2});

        auto omit_bridge_lemmas = std::holds_alternative<equals_proof_mutation::OmitBridgeLemmas>(mutation);
        auto bridge = [logger, omit_bridge_lemmas](const auto & pruned, const auto & other, Integer lo, Integer hi, const ReasonLiterals & r) {
            if (omit_bridge_lemmas)
                return; // testing only: leaves the conclusion claiming to be RUP unaided
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
                        JustifyExplicitly{
                            [=](const ReasonLiterals & r) { bridge(pruned, other, lo, hi, r); }, ThenRUP::Yes, hints::EqualsNotInRange{{owner}}},
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
        const ConstraintID & owner, bool want_reasons, EqualsProofMutation mutation) -> pair<hints::EqualsNoOverlap, Reason>
    {
        hints::EqualsNoOverlap no_overlap{{owner}, v1, v2, cond, mutation};

        // Assembling the reason is linear in the length of the witness, and it
        // is the *only* walk of the domains: emit_justification re-reads the
        // walk out of the literals below rather than doing it again. This one
        // sits on the propagation path, so with proofs off it is built, never
        // read, and thrown away. That is the situation want_reasons() exists for, and when
        // this witness was per-value the cost was not academic: issue #864
        // measured 78 GB and 160 s at width 10^9, and a bad_alloc on a smaller
        // machine. The must-not-hold pass below was guarded for the same reason
        // in fea9508d; this call site was missed.
        if (! want_reasons)
            return pair{no_overlap, Reason{}};

        // State's own iterators are not involved -- this walks domains directly
        // -- so the audit lane cannot see it without saying so.
        LargeDomainIterationCounter guard{"the number of literals one reified equals no-overlap reason has walked"};
        ReasonLiterals reason;

        // A run of values one operand cannot take is one range condition -- unless
        // that operand is a view, which has no range literal (#882), in which case
        // it is spelled out, the same degradation generic_reason and
        // ProofLogger::infer already make. Only the run is spelled out: the rest of
        // the walk is unaffected, so a view pays for its own holes and not for the
        // width of anything.
        //
        // The witness does not care which spelling a run got. Stepping `v1 >= lo`
        // to `v1 >= hi + 1` is the range literal's reverse reification in one case
        // and the eq atoms walking the order chain in the other; either way it is
        // internal to that variable and needs no lemma from us. Which is why this
        // is a fallback in the reason and nowhere else.
        auto skip_run = [&](IntegerVariableID var, Integer lo, Integer hi) {
            if (lo == hi || ! std::holds_alternative<ViewOfIntegerVariableID>(var)) {
                guard.step();
                reason.emplace_back(not_in_range(var, lo, hi));
            }
            else
                for (auto val = lo; val <= hi; ++val) {
                    guard.step();
                    reason.emplace_back(var != val);
                }
        };

        // One literal per move of the walk: the runs that make the two domains
        // disjoint, rather than the values in them. In the common shape -- two
        // hole-free domains lying on opposite sides of some point -- that is the
        // two bounds that separate them and nothing else.
        walk_no_overlap(state.copy_of_values(v1), state.copy_of_values(v2), [&](NoOverlapStep kind, Integer lo, Integer hi) {
            switch (kind) {
            case NoOverlapStep::AnchorV1Lower:
                guard.step();
                reason.emplace_back(v1 >= lo);
                break;
            case NoOverlapStep::JumpToV2Lower:
                guard.step();
                reason.emplace_back(v2 >= lo);
                break;
            case NoOverlapStep::SkipV1Hole: skip_run(v1, lo, hi); break;
            case NoOverlapStep::SkipV2Hole: skip_run(v2, lo, hi); break;
            case NoOverlapStep::StopAboveV1Upper:
                guard.step();
                reason.emplace_back(v1 <= lo);
                break;
            case NoOverlapStep::StopAboveV2Upper:
                guard.step();
                reason.emplace_back(v2 <= lo);
                break;
            }
        });

        // Testing only: the walk's last literal is its stop, so without it the
        // reason climbs to a position and never says the position is impossible.
        // See EqualsProofMutation.
        if (std::holds_alternative<equals_proof_mutation::DropNoOverlapStopLiteral>(mutation) && ! reason.empty())
            reason.pop_back();

        return pair{no_overlap, ExplicitReason{reason}};
    }

    // equals's reified verdicts are either a plain RUP (the singleton / forced
    // cases) or the no-overlap witness; a variant of the two, visited inside infer.
    using EqualsJustification = std::variant<JustifyUsingRUP<hints::Equals>, JustifyExplicitly<hints::EqualsNoOverlap>>;
}

ReifiedEquals::ReifiedEquals(const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool neq) :
    _v1(v1), _v2(v2), _cond(cond), _neq(neq)
{
}

auto ReifiedEquals::with_proof_mutation(const EqualsProofMutation mutation) -> ReifiedEquals &
{
    _proof_mutation = mutation;
    return *this;
}

auto ReifiedEquals::clone() const -> unique_ptr<Constraint>
{
    // _neq must come along: both Problem::post and Problem::create_propagators
    // clone, so a clone that drops it is the only ReifiedEquals anything ever
    // reads, and the flag is false everywhere it is asked (issue #865). It
    // controls the written description, not the propagation -- the semantic
    // flip lives in the derived constructors' negated conditions -- so dropping
    // it made a NotEqualsIff describe itself as an equals_iff over a negated
    // condition, which is the same constraint said backwards.
    auto cloned = make_unique<ReifiedEquals>(_v1, _v2, _cond, _neq);
    cloned->with_proof_mutation(_proof_mutation);
    return cloned;
}

auto ReifiedEquals::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _evaluated_cond = test_reification_condition(initial_state, _cond);
    return true;
}

auto ReifiedEquals::define_proof_model(ProofModel & model, const State &) -> void
{
    overloaded{
        [&](const reif::MustHold &) {
            // cake_pb_cp: V1 = V2 split into le (V1 <= V2) and ge (V1 >= V2).
            model.add_labelled_constraint(_constraint_id, "le", "ge", WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i);
        }, //
        [&](const reif::MustNotHold &) {
            // cake_pb_cp: V1 != V2 split into gt (V1 > V2) and lt (V1 < V2) on a
            // single per-constraint selector b[id][ne] (cake's `nev`): the flag
            // true selects the gt half, false the lt half.
            auto neflag = model.create_proof_flag(_constraint_id, "ne");
            model.add_labelled_constraint(_constraint_id, "gt", WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 1_i, HalfReifyOnConjunctionOf{{neflag}});
            model.add_labelled_constraint(_constraint_id, "lt", WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= -1_i, HalfReifyOnConjunctionOf{{! neflag}});
        }, //
        [&](const reif::If & reif) {
            // cake_pb_cp's encode_equal (-if): the equality split le (V1 <= V2) and
            // ge (V1 >= V2), each half-reified on the condition. Labelled @c[id][le] /
            // @c[id][ge] to match cake's cencode_equal_1.
            model.add_labelled_constraint(
                _constraint_id, "le", "ge", WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i, HalfReifyOnConjunctionOf{{reif.cond}});
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
            model.add_labelled_constraint(_constraint_id, "al1", WPBSum{} + 1_i * ltflag + 1_i * gtflag + 1_i * ! reif.cond >= 1_i);
        }, //
        [&](const reif::Iff & reif) {
            // cake_pb_cp's encode_equal (-iff): the equality split le/ge half-reified on
            // the condition (@c[id][le] / @c[id][ge], cencode_equal_1); per-side selectors
            // b[id][gt] / b[id][lt] half-implying the strict comparisons (cake's gtv/ltv
            // via cvar_imply, each labelled with the flag's own name + [r]); and an
            // at-least-one @c[id][al1] tying lt, gt and the condition together.
            model.add_labelled_constraint(
                _constraint_id, "le", "ge", WPBSum{} + (1_i * _v1) + (-1_i * _v2) == 0_i, HalfReifyOnConjunctionOf{{reif.cond}});

            auto gtflag = model.create_proof_flag(_constraint_id, "gt");
            model.add_labelled_constraint(model.names_and_ids_tracker().pb_file_string_for(gtflag) + "[r]",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) >= 1_i, HalfReifyOnConjunctionOf{{gtflag}});
            auto ltflag = model.create_proof_flag(_constraint_id, "lt");
            model.add_labelled_constraint(model.names_and_ids_tracker().pb_file_string_for(ltflag) + "[r]",
                WPBSum{} + (1_i * _v1) + (-1_i * _v2) <= -1_i, HalfReifyOnConjunctionOf{{ltflag}});

            model.add_labelled_constraint(_constraint_id, "al1", WPBSum{} + 1_i * ltflag + 1_i * gtflag + 1_i * reif.cond >= 1_i);
        } //
    }
        .visit(_cond);
}

auto ReifiedEquals::install_propagators(Propagators & propagators) -> void
{
    auto enforce_constraint_must_hold = [v1 = _v1, v2 = _v2, owner = constraint_id(), mutation = _proof_mutation](const State & state,
                                            auto & inference, ProofLogger * const logger, const Literal & cond) -> PropagatorState {
        return visit(
            [&](auto & v1, auto & v2) { return enforce_equality(logger, v1, v2, state, inference, ReasonLiterals{cond}, owner, mutation); }, v1, v2);
    };

    auto enforce_constraint_must_not_hold = [v1 = _v1, v2 = _v2, owner = constraint_id()](const State & state, auto & inference,
                                                ProofLogger * const logger, const Literal & cond) -> PropagatorState {
        auto value1 = state.optional_single_value(v1);
        if (value1) {
            // The reason is stated outright -- the value is already in hand, so
            // deferring through ExactSingleValue would only re-read the domain
            // at materialise time, and both literals sit inline.
            if (! inference.infer_not_equal_or_stop(logger, v2, *value1, JustifyUsingRUP{hints::Equals{owner}},
                    inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{cond, v1 == *value1}}} : Reason{}))
                return PropagatorState::Enable; // contradiction: loop sees tracker.contradicted()
            return PropagatorState::DisableUntilBacktrack;
        }
        auto value2 = state.optional_single_value(v2);
        if (value2) {
            if (! inference.infer_not_equal_or_stop(logger, v1, *value2, JustifyUsingRUP{hints::Equals{owner}},
                    inference.want_reasons() ? Reason{ExplicitReason{ReasonLiterals{cond, v2 == *value2}}} : Reason{}))
                return PropagatorState::Enable; // contradiction: loop sees tracker.contradicted()
            return PropagatorState::DisableUntilBacktrack;
        }
        return PropagatorState::Enable;
    };

    auto infer_cond_when_undecided = [v1 = _v1, v2 = _v2, owner = constraint_id(), mutation = _proof_mutation](const State & state, auto & inference,
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
            auto reason = Reason{ExplicitReason{ReasonLiterals{v1 == *value1, v2 == *value2}}};
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
                auto [no_overlap, reason] = no_overlap_justification(state, logger, v1, v2, cond, owner, inference.want_reasons(), mutation);
                return reification_verdict::MustNotHold<EqualsJustification>{
                    .justification = JustifyExplicitly{no_overlap, ThenRUP::Yes}, //
                    .reason = reason                                              //
                };
            }
            return reification_verdict::StillUndecided{};
        }
    };

    // on_change for the shared set, because the undecided pass reads in_domain and
    // domains_intersect, and the must-hold pass intersects the two domains.
    //
    // Unless one operand is a constant, which collapses both of those reads. With
    // v2 pinned at c its optional_single_value is always set, so the undecided pass
    // never reaches the domains_intersect arm at all: it reports MustHold exactly
    // when v1 is instantiated to c, and MustNotHold exactly when c leaves v1's
    // domain -- its "v1 fixed to something other than c" and "! in_domain(v1, c)"
    // arms being the same fact stated twice, since fixing v1 elsewhere removes c.
    // The must-hold pass likewise finds the constant's single value and fixes v1 to
    // it on its first wake, and the must-not-hold pass removes it, both returning
    // DisableUntilBacktrack, so once the condition is decided the condition's own
    // trigger is all that arm ever needs.
    //
    // So the propagator turns on two facts about the other operand: whether it is
    // instantiated, and whether c is still in its domain. on_instantiated covers
    // the first -- every State::change_state_for_* that leaves a domain a singleton
    // reports Inference::Instantiated, whichever operation got it there. A refined
    // watch on `other != c` covers the second, and wakes only the propagator whose
    // value was the one removed, where on_change wakes every propagator posted on
    // that variable. In a model that posts a reified equality per (variable, value)
    // pair -- FlatZinc's int_eq_reif against a constant, which is what
    // `x == sum(bool2int(xs[i] == v))` flattens to -- that is the difference
    // between one wake per interior removal and one per value in the domain
    // (issue #889).
    //
    // Two constant operands need no special case: on_change registers no wake for a
    // constant either, and every pass decides outright on the one call every
    // propagator gets when search starts.
    Triggers triggers;
    if (is_constant_variable(_v1) != is_constant_variable(_v2)) {
        auto [other, constant] = is_constant_variable(_v2) ? pair{_v1, constant_value_of(_v2)} : pair{_v2, constant_value_of(_v1)};
        triggers.on_instantiated = {_v1, _v2};
        triggers.refined.emplace_back(other != constant, 0u);
    }
    else
        triggers.on_change = {_v1, _v2};

    // An unconditional NotEquals, constant operand or not, only ever runs the
    // must-not-hold pass, which reads nothing but optional_single_value and
    // disables itself until backtrack once it has acted -- so on_instantiated
    // cannot miss its wake, and the wakes it drops are the expensive ones: fixing
    // a vertex removes one value from each of its d neighbours, and under
    // on_change each of those interior removals woke every other not-equals on
    // that neighbour to find neither end fixed (issue #819).
    Triggers triggers_when_must_not_hold;
    triggers_when_must_not_hold.on_instantiated = {_v1, _v2};

    install_reified_dispatcher(propagators, constraint_id(), _evaluated_cond, _cond, triggers, std::move(enforce_constraint_must_hold),
        std::move(enforce_constraint_must_not_hold), std::move(infer_cond_when_undecided), std::move(triggers_when_must_not_hold));
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

auto ReifiedEquals::constraint_type() const -> std::string
{
    return overloaded{
        [](const reif::MustHold &) -> string { return "equals"; },                  //
        [](const reif::MustNotHold &) -> string { return "not_equals"; },           //
        [](const reif::If &) -> string { return "equals"; },                        //
        [](const reif::NotIf &) -> string { return "not_equals"; },                 //
        [&](const reif::Iff &) -> string { return _neq ? "not_equals" : "equals"; } //
    }
        .visit(_cond);
}

auto ReifiedEquals::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    string head = constraint_type() +
        overloaded{
            [](const reif::MustHold &) -> string { return ""; },    //
            [](const reif::MustNotHold &) -> string { return ""; }, //
            [](const reif::If &) -> string { return "_if"; },       //
            [](const reif::NotIf &) -> string { return "_if"; },    //
            [](const reif::Iff &) -> string { return "_iff"; }      //
        }
            .visit(_cond);

    // A not-equals iff stores the negated condition (equality holds iff NOT the
    // user's condition), but the not_equals_iff keyword already carries the
    // negation: cake reads (r not_equals_iff (cond) v1 v2) as cond <=> v1 != v2.
    // Emit the user's original condition, not the stored one, or the two
    // negations cancel into the opposite constraint.
    auto cond_to_write =
        _neq && std::holds_alternative<reif::Iff>(_cond) ? ReificationCondition{reif::Iff{! std::get<reif::Iff>(_cond).cond}} : _cond;
    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(head)};
    if (auto cond = tracker.s_expr_term_of(cond_to_write))
        terms.push_back(std::move(*cond));
    terms.push_back(tracker.s_expr_term_of(_v1));
    terms.push_back(tracker.s_expr_term_of(_v2));

    return SExpr::list(std::move(terms));
}

template auto gcs::innards::enforce_equality(ProofLogger * const logger, const IntegerVariableID & v1, const IntegerVariableID & v2,
    const State & state, SimpleInferenceTracker & inference, const ReasonLiterals & reason, const ConstraintID & owner, EqualsProofMutation mutation)
    -> PropagatorState;
template auto gcs::innards::enforce_equality(ProofLogger * const logger, const IntegerVariableID & v1, const IntegerVariableID & v2,
    const State & state, EagerProofLoggingInferenceTracker & inference, const ReasonLiterals & reason, const ConstraintID & owner,
    EqualsProofMutation mutation) -> PropagatorState;
