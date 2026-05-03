#include <gcs/constraints/lex.hh>
#include <gcs/constraints/innards/reified_dispatcher.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <memory>
#include <optional>
#include <sstream>
#include <utility>
#include <variant>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::any_cast;
using std::get;
using std::make_shared;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;
using std::visit;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

using namespace gcs;
using namespace gcs::innards;

namespace
{
    struct LexState
    {
        size_t alpha = 0;
    };

    // One propagation pass enforcing vars_1 (>|>=)_lex vars_2. This is the
    // forward direction from the propagator's point of view; for backward
    // (negation) propagation, callers swap vars_1/vars_2 and flip or_equal.
    auto run_lex_pass(
        const State & state,
        auto & inference,
        ProofLogger * const logger,
        const vector<IntegerVariableID> & vars_1,
        const vector<IntegerVariableID> & vars_2,
        bool or_equal,
        const shared_ptr<vector<optional<ProofFlag>>> & prefix_equal_flags,
        const shared_ptr<vector<ProofFlag>> & decision_at_flags,
        const Literal & cond,
        ConstraintStateHandle state_handle) -> PropagatorState
    {
        auto n = min(vars_1.size(), vars_2.size());

        auto & lex_state = any_cast<LexState &>(state.get_constraint_state(state_handle));
        auto alpha = lex_state.alpha;

        // Advance alpha through any newly-forced-equal positions. No
        // inferences happen here: those positions had vars_1[k] = vars_2[k]
        // forced by a prior call (or by branching), so the bounds in the
        // reason already imply ~decision_at[k] for all k < alpha.
        while (alpha < n) {
            auto b1 = state.bounds(vars_1[alpha]);
            auto b2 = state.bounds(vars_2[alpha]);
            if (b1.first == b1.second && b2.first == b2.second && b1.first == b2.first)
                ++alpha;
            else
                break;
        }

        auto all_vars = vars_1;
        all_vars.insert(all_vars.end(), vars_2.begin(), vars_2.end());
        auto reason = bounds_reason(state, all_vars, cond);

        // For non-strict, walking off the end means all positions are forced
        // equal, which is itself a valid solution. The constraint is now
        // fully discharged.
        if (alpha == n) {
            lex_state.alpha = alpha;
            if (or_equal)
                return PropagatorState::DisableUntilBacktrack;

            // Strict variant: walked off with everything equal, infeasible.
            auto contradiction_proof = [&, n](const ReasonFunction & r) -> void {
                if (! logger) return;
                for (size_t k = 0; k < n; ++k)
                    logger->emit_rup_proof_line_under_reason(r,
                        WPBSum{} + 1_i * ! decision_at_flags->at(k) >= 1_i,
                        ProofLevel::Temporary);
            };
            inference.contradiction(logger, JustifyExplicitlyThenRUP{contradiction_proof}, reason);
        }

        auto emit_not_d = [&](const ReasonFunction & r, size_t k) -> void {
            logger->emit_rup_proof_line_under_reason(r,
                WPBSum{} + 1_i * ! decision_at_flags->at(k) >= 1_i,
                ProofLevel::Temporary);
        };

        bool strict_forced = false;

        // Tighten at alpha (the >= part of the constraint): vars_1[alpha] must
        // be at least vars_2[alpha].lo, and vars_2[alpha] at most vars_1[alpha].hi.
        auto b1_alpha = state.bounds(vars_1[alpha]);
        auto b2_alpha = state.bounds(vars_2[alpha]);

        auto tighten_proof = [&, alpha](const ReasonFunction & r) -> void {
            if (! logger) return;
            for (size_t k = 0; k < alpha; ++k)
                emit_not_d(r, k);
            for (size_t k = alpha; k < n; ++k) {
                logger->emit_rup_proof_line_under_reason(r,
                    WPBSum{} + 1_i * (vars_1[alpha] >= b2_alpha.first) + 1_i * ! *prefix_equal_flags->at(k + 1) >= 1_i,
                    ProofLevel::Temporary);
                logger->emit_rup_proof_line_under_reason(r,
                    WPBSum{} + 1_i * (vars_2[alpha] < b1_alpha.second + 1_i) + 1_i * ! *prefix_equal_flags->at(k + 1) >= 1_i,
                    ProofLevel::Temporary);
            }
        };

        inference.infer_all(logger,
            {vars_1[alpha] >= b2_alpha.first, vars_2[alpha] < b1_alpha.second + 1_i},
            JustifyExplicitlyThenRUP{tighten_proof}, reason);

        auto nb1_alpha = state.bounds(vars_1[alpha]);
        auto nb2_alpha = state.bounds(vars_2[alpha]);

        if (nb1_alpha.first > nb2_alpha.second) {
            strict_forced = true;
        }
        else {
            bool found_beta = false;
            bool prefix_blocked = false;
            size_t blocking_position = n;
            for (size_t k = alpha + 1; k < n; ++k) {
                auto bk1 = state.bounds(vars_1[k]);
                auto bk2 = state.bounds(vars_2[k]);
                if (bk1.second > bk2.first) {
                    found_beta = true;
                    break;
                }
                if (bk1.second < bk2.first) {
                    prefix_blocked = true;
                    blocking_position = k;
                    break;
                }
            }

            bool must_force_strict = (! found_beta) && ((! or_equal) || prefix_blocked);

            if (must_force_strict) {
                bool alpha_candidate = (nb1_alpha.second > nb2_alpha.first);

                auto emit_not_prefix_equal_for_or_equal = [&](const ReasonFunction & r) -> void {
                    if (or_equal && prefix_blocked)
                        logger->emit_rup_proof_line_under_reason(r,
                            WPBSum{} + 1_i * ! *prefix_equal_flags->at(blocking_position + 1) >= 1_i,
                            ProofLevel::Temporary);
                };

                if (! alpha_candidate) {
                    auto contradiction_proof = [&, n](const ReasonFunction & r) -> void {
                        if (! logger) return;
                        for (size_t k = 0; k < n; ++k)
                            emit_not_d(r, k);
                        emit_not_prefix_equal_for_or_equal(r);
                    };
                    inference.contradiction(logger, JustifyExplicitlyThenRUP{contradiction_proof}, reason);
                }

                auto force_strict_proof = [&, alpha, n](const ReasonFunction & r) -> void {
                    if (! logger) return;
                    for (size_t k = 0; k < n; ++k) {
                        if (k == alpha) continue;
                        emit_not_d(r, k);
                    }
                    emit_not_prefix_equal_for_or_equal(r);
                };

                inference.infer_all(logger,
                    {vars_1[alpha] >= nb2_alpha.first + 1_i,
                        vars_2[alpha] < nb1_alpha.second},
                    JustifyExplicitlyThenRUP{force_strict_proof}, reason);

                auto fb1 = state.bounds(vars_1[alpha]);
                auto fb2 = state.bounds(vars_2[alpha]);
                if (fb1.first > fb2.second)
                    strict_forced = true;
            }
        }

        lex_state.alpha = alpha;

        return strict_forced ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable;
    }

    // Emit RUP scaffolding to convince VeriPB that, under the given reason,
    // the encoding of "vars_1 (>|>=)_lex vars_2" cannot be satisfied —
    // forcing all decision_at flags to FALSE, plus ~prefix_equal[k0+1] at
    // the first not-equal position so VeriPB can chain it through to
    // ~prefix_equal[n]. Used when inferring the reification literal: under
    // the negation of the inferred cond, the half-reified at-least-one
    // constraint becomes active and conflicts with the bounds-forced aux
    // flag values.
    auto emit_lex_unsat_scaffold(
        const State & state,
        ProofLogger * const logger,
        const ReasonFunction & r,
        const vector<IntegerVariableID> & vars_1,
        const vector<IntegerVariableID> & vars_2,
        size_t n,
        const shared_ptr<vector<optional<ProofFlag>>> & prefix_equal_flags,
        const shared_ptr<vector<ProofFlag>> & decision_at_flags) -> void
    {
        // First not-equal position (where bounds prevent vars_1[k0] =
        // vars_2[k0]). ~prefix_equal[k0+1] is RUP-derivable directly from
        // bounds and the prefix_equal half-reif at k0.
        for (size_t k = 0; k < n; ++k) {
            auto b1 = state.bounds(vars_1[k]);
            auto b2 = state.bounds(vars_2[k]);
            bool fixed_equal = (b1.first == b1.second && b2.first == b2.second && b1.first == b2.first);
            if (fixed_equal)
                continue;
            // Bounds force inequality iff there's no overlap.
            if (b1.first > b2.second || b1.second < b2.first) {
                logger->emit_rup_proof_line_under_reason(r,
                    WPBSum{} + 1_i * ! *prefix_equal_flags->at(k + 1) >= 1_i,
                    ProofLevel::Temporary);
            }
            break;
        }

        // ~decision_at[k] for every position. Each is RUP-derivable directly
        // from bounds (decision_at[k] -> prefix_equal[k] AND vars_1[k] >
        // vars_2[k]; one of these always conflicts under the assumed bounds,
        // chaining via the just-emitted ~prefix_equal[k0+1] for k > k0).
        for (size_t k = 0; k < n; ++k)
            logger->emit_rup_proof_line_under_reason(r,
                WPBSum{} + 1_i * ! decision_at_flags->at(k) >= 1_i,
                ProofLevel::Temporary);
    }

    // Detection-only logic for when the reification condition is undecided.
    // Walk through positions: if we can prove the constraint definitely
    // holds (or definitely doesn't hold) from the current bounds, return
    // the appropriate verdict (carrying the materials for the dispatcher
    // to use if it decides to infer the cond literal). Otherwise, return
    // StillUndecided.
    auto run_lex_undecided_detection(
        const State & state,
        ProofLogger * const logger,
        const vector<IntegerVariableID> & vars_1,
        const vector<IntegerVariableID> & vars_2,
        bool or_equal,
        const shared_ptr<vector<optional<ProofFlag>>> & prefix_equal_gt_flags,
        const shared_ptr<vector<ProofFlag>> & decision_at_gt_flags,
        const shared_ptr<vector<optional<ProofFlag>>> & prefix_equal_lt_flags,
        const shared_ptr<vector<ProofFlag>> & decision_at_lt_flags,
        const IntegerVariableCondition & cond) -> ReificationVerdict
    {
        auto n = min(vars_1.size(), vars_2.size());

        auto all_vars = vars_1;
        all_vars.insert(all_vars.end(), vars_2.begin(), vars_2.end());
        auto reason = bounds_reason(state, all_vars);

        size_t k = 0;
        bool definitely_holds = false;
        bool definitely_does_not_hold = false;

        for (; k < n; ++k) {
            auto b1 = state.bounds(vars_1[k]);
            auto b2 = state.bounds(vars_2[k]);

            bool fixed_equal = (b1.first == b1.second && b2.first == b2.second && b1.first == b2.first);
            if (fixed_equal)
                continue;

            if (b1.first > b2.second) {
                // Strict-greater forced at first non-equal position: constraint
                // (>=, or strict >) definitely holds.
                definitely_holds = true;
            }
            else if (b1.second < b2.first) {
                // Strict-less forced: constraint definitely does not hold.
                definitely_does_not_hold = true;
            }
            // else: bounds overlap, leave the determination to a later call
            // once tighter bounds arrive.
            break;
        }

        if (k == n) {
            // All positions forced equal: constraint holds for non-strict,
            // does not hold for strict.
            if (or_equal)
                definitely_holds = true;
            else
                definitely_does_not_hold = true;
        }

        if (! definitely_holds && ! definitely_does_not_hold)
            return reification_verdict::StillUndecided{};

        // When the dispatcher infers cond, the framework's RUP step will
        // assume the *negation* of the inferred literal. The scaffolding
        // therefore lives under that negation: the opposite-direction
        // encoding's at-least-one is then active, and the bounds force
        // every aux flag to FALSE, violating it. We pre-emit those
        // ~aux_flag lines so VeriPB's PB unit propagation can chain.
        if (definitely_holds) {
            auto reason_under_cond_false = [base = reason, cond]() {
                auto rl = base();
                rl.push_back(! cond);
                return rl;
            };
            auto justify = [&state, logger, vars_1, vars_2, n,
                               prefix_equal_lt_flags, decision_at_lt_flags,
                               reason_under_cond_false](const ReasonFunction &) -> void {
                if (logger && prefix_equal_lt_flags && decision_at_lt_flags)
                    emit_lex_unsat_scaffold(state, logger, ReasonFunction{reason_under_cond_false},
                        vars_2, vars_1, n,
                        prefix_equal_lt_flags, decision_at_lt_flags);
            };
            return reification_verdict::MustHold{
                .justification = JustifyExplicitlyThenRUP{justify},
                .reason = std::move(reason)};
        }
        else {
            auto reason_under_cond_true = [base = reason, cond]() {
                auto rl = base();
                rl.push_back(cond);
                return rl;
            };
            auto justify = [&state, logger, vars_1, vars_2, n,
                               prefix_equal_gt_flags, decision_at_gt_flags,
                               reason_under_cond_true](const ReasonFunction &) -> void {
                if (logger && prefix_equal_gt_flags && decision_at_gt_flags)
                    emit_lex_unsat_scaffold(state, logger, ReasonFunction{reason_under_cond_true},
                        vars_1, vars_2, n,
                        prefix_equal_gt_flags, decision_at_gt_flags);
            };
            return reification_verdict::MustNotHold{
                .justification = JustifyExplicitlyThenRUP{justify},
                .reason = std::move(reason)};
        }
    }

    struct DirectionFlags
    {
        // prefix_equal[0] is the empty-prefix flag — trivially TRUE — so
        // we don't bother creating a ProofFlag for it; element 0 is
        // nullopt. Indices 1..n are real ProofFlag instances.
        shared_ptr<vector<optional<ProofFlag>>> prefix_equal;
        shared_ptr<vector<ProofFlag>> decision_at;
    };

    struct EncodingFlags
    {
        DirectionFlags gt;
        DirectionFlags lt;
    };

    // Build the OPB encoding for one "direction" of the lex constraint.
    // The direction here is "vars_1 (>|>=)_lex vars_2" with the given
    // or_equal flag, and the encoding optionally half-reified on a cond
    // literal (so that under !cond, all aux constraints are vacuous and
    // the aux flags can take any value).
    //
    // The half-reify is applied to *every* aux constraint, not just the
    // global at-least-one disjunction: this ensures that under a
    // hypothetical "cond=FALSE" assignment, VeriPB can verify a solution
    // by leaving the aux flags entirely unconstrained, rather than
    // tripping over residual implications between them.
    auto build_lex_direction_encoding(
        ProofModel & model,
        const vector<IntegerVariableID> & vars_1,
        const vector<IntegerVariableID> & vars_2,
        bool or_equal,
        const optional<HalfReifyOnConjunctionOf> & cond_half_reify,
        const string & flag_prefix) -> DirectionFlags
    {
        auto n = min(vars_1.size(), vars_2.size());

        DirectionFlags d;
        d.prefix_equal = make_shared<vector<optional<ProofFlag>>>();
        d.decision_at = make_shared<vector<ProofFlag>>();
        d.prefix_equal->push_back(nullopt);
        for (size_t i = 1; i <= n; ++i)
            d.prefix_equal->push_back(model.create_proof_flag(format("lex_{}_prefix_equal_{}", flag_prefix, i)));
        for (size_t i = 0; i < n; ++i)
            d.decision_at->push_back(model.create_proof_flag(format("lex_{}_decision_at_{}", flag_prefix, i)));

        auto with_cond = [&](HalfReifyOnConjunctionOf base) {
            if (cond_half_reify)
                base.insert(base.end(), cond_half_reify->begin(), cond_half_reify->end());
            return base;
        };

        // No "prefix_equal[0] >= 1" constraint needed: prefix_equal[0] is
        // the empty-prefix-is-equal flag, trivially TRUE. Likewise the
        // chain and decision_at aux defs at i=0 reduce to "X -> TRUE" and
        // are skipped.
        for (size_t i = 0; i < n; ++i) {
            if (i > 0) {
                // prefix_equal[i+1] -> prefix_equal[i]
                model.add_constraint(
                    WPBSum{} + 1_i * *d.prefix_equal->at(i) >= 1_i,
                    with_cond(HalfReifyOnConjunctionOf{*d.prefix_equal->at(i + 1)}));

                // decision_at[i] -> prefix_equal[i]
                model.add_constraint(
                    WPBSum{} + 1_i * *d.prefix_equal->at(i) >= 1_i,
                    with_cond(HalfReifyOnConjunctionOf{d.decision_at->at(i)}));
            }

            // prefix_equal[i+1] -> vars_1[i] = vars_2[i]
            model.add_constraint(
                WPBSum{} + 1_i * vars_1[i] + -1_i * vars_2[i] == 0_i,
                with_cond(HalfReifyOnConjunctionOf{*d.prefix_equal->at(i + 1)}));

            // decision_at[i] -> vars_1[i] > vars_2[i]
            model.add_constraint(
                WPBSum{} + 1_i * vars_1[i] + -1_i * vars_2[i] >= 1_i,
                with_cond(HalfReifyOnConjunctionOf{d.decision_at->at(i)}));
        }

        // At-least-one: cond -> sum decision_at + (or_equal ? prefix_equal[n] : 0) >= 1.
        WPBSum at_least_one;
        for (auto & da : *d.decision_at)
            at_least_one += 1_i * da;
        if (or_equal)
            at_least_one += 1_i * *d.prefix_equal->at(n);
        model.add_constraint(move(at_least_one) >= 1_i, cond_half_reify);

        return d;
    }
}

LexCompareGreaterThanOrMaybeEqual::LexCompareGreaterThanOrMaybeEqual(
    vector<IntegerVariableID> vars_1, vector<IntegerVariableID> vars_2,
    ReificationCondition reif_cond, bool or_equal, bool vars_swapped) :
    _vars_1(move(vars_1)),
    _vars_2(move(vars_2)),
    _reif_cond(reif_cond),
    _or_equal(or_equal),
    _vars_swapped(vars_swapped)
{
}

auto LexCompareGreaterThanOrMaybeEqual::clone() const -> unique_ptr<Constraint>
{
    return make_unique<LexCompareGreaterThanOrMaybeEqual>(_vars_1, _vars_2, _reif_cond, _or_equal, _vars_swapped);
}

auto LexCompareGreaterThanOrMaybeEqual::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto or_equal = _or_equal;

    // Decide which directions of the encoding we need based on the
    // reification type. If always picks just the constraint direction;
    // NotIf picks the negation; Iff picks both.
    bool need_gt_direction = false;
    bool need_lt_direction = false;
    optional<HalfReifyOnConjunctionOf> half_reify_for_gt;
    optional<HalfReifyOnConjunctionOf> half_reify_for_lt;

    overloaded{
        [&](const reif::MustHold &) {
            need_gt_direction = true;
        },
        [&](const reif::MustNotHold &) {
            need_lt_direction = true;
        },
        [&](const reif::If & r) {
            need_gt_direction = true;
            half_reify_for_gt = HalfReifyOnConjunctionOf{r.cond};
        },
        [&](const reif::NotIf & r) {
            need_lt_direction = true;
            half_reify_for_lt = HalfReifyOnConjunctionOf{r.cond};
        },
        [&](const reif::Iff & r) {
            need_gt_direction = true;
            need_lt_direction = true;
            half_reify_for_gt = HalfReifyOnConjunctionOf{r.cond};
            half_reify_for_lt = HalfReifyOnConjunctionOf{! r.cond};
        }}
        .visit(_reif_cond);

    EncodingFlags flags;
    if (optional_model) {
        if (need_gt_direction)
            flags.gt = build_lex_direction_encoding(*optional_model,
                _vars_1, _vars_2, _or_equal, half_reify_for_gt, "gt");
        if (need_lt_direction)
            flags.lt = build_lex_direction_encoding(*optional_model,
                _vars_2, _vars_1, ! _or_equal, half_reify_for_lt, "lt");
    }
    auto prefix_equal_gt_flags = flags.gt.prefix_equal;
    auto decision_at_gt_flags = flags.gt.decision_at;
    auto prefix_equal_lt_flags = flags.lt.prefix_equal;
    auto decision_at_lt_flags = flags.lt.decision_at;

    Triggers triggers;
    for (auto & v : _vars_1)
        triggers.on_bounds.push_back(v);
    for (auto & v : _vars_2)
        triggers.on_bounds.push_back(v);

    auto state_handle = initial_state.add_constraint_state(LexState{});

    auto enforce_constraint_must_hold = [vars_1 = _vars_1, vars_2 = _vars_2, or_equal,
                                            prefix_equal_gt_flags, decision_at_gt_flags, state_handle](
                                            const State & state, auto & inference, ProofLogger * const logger,
                                            const Literal & cond) -> PropagatorState {
        return run_lex_pass(state, inference, logger,
            vars_1, vars_2, or_equal,
            prefix_equal_gt_flags, decision_at_gt_flags,
            cond, state_handle);
    };

    auto enforce_constraint_must_not_hold = [vars_1 = _vars_1, vars_2 = _vars_2, or_equal,
                                                prefix_equal_lt_flags, decision_at_lt_flags, state_handle](
                                                const State & state, auto & inference, ProofLogger * const logger,
                                                const Literal & cond) -> PropagatorState {
        // Negation: enforce vars_2 (>|>=) vars_1 with or_equal flipped.
        return run_lex_pass(state, inference, logger,
            vars_2, vars_1, ! or_equal,
            prefix_equal_lt_flags, decision_at_lt_flags,
            cond, state_handle);
    };

    auto infer_cond_when_undecided = [vars_1 = move(_vars_1), vars_2 = move(_vars_2), or_equal,
                                         prefix_equal_gt_flags, decision_at_gt_flags,
                                         prefix_equal_lt_flags, decision_at_lt_flags](
                                         const State & state, auto &, ProofLogger * const logger,
                                         const IntegerVariableCondition & cond) -> ReificationVerdict {
        return run_lex_undecided_detection(state, logger,
            vars_1, vars_2, or_equal,
            prefix_equal_gt_flags, decision_at_gt_flags,
            prefix_equal_lt_flags, decision_at_lt_flags,
            cond);
    };

    install_reified_dispatcher(propagators, initial_state.test_reification_condition(_reif_cond), _reif_cond, triggers,
        std::move(enforce_constraint_must_hold),
        std::move(enforce_constraint_must_not_hold),
        std::move(infer_cond_when_undecided),
        "lex");
}

auto LexCompareGreaterThanOrMaybeEqual::s_exprify(const std::string & name, const innards::ProofModel * const model) const -> std::string
{
    stringstream s;

    string reif_suffix = overloaded{
        [](const reif::MustHold &) -> string { return ""; },
        [](const reif::MustNotHold &) -> string { return "_not"; },
        [](const reif::If &) -> string { return "_if"; },
        [](const reif::NotIf &) -> string { return "_not_if"; },
        [](const reif::Iff &) -> string { return "_iff"; }}
                             .visit(_reif_cond);

    string cmp = format("lex_{}_than{}{}",
        _vars_swapped ? "less" : "greater",
        _or_equal ? "_equal" : "",
        reif_suffix);

    print(s, "{} {}", name, cmp);

    auto cond_lit = overloaded{
        [](const reif::MustHold &) -> optional<IntegerVariableCondition> { return nullopt; },
        [](const reif::MustNotHold &) -> optional<IntegerVariableCondition> { return nullopt; },
        [](const reif::If & r) -> optional<IntegerVariableCondition> { return r.cond; },
        [](const reif::NotIf & r) -> optional<IntegerVariableCondition> { return r.cond; },
        [](const reif::Iff & r) -> optional<IntegerVariableCondition> { return r.cond; }}
                        .visit(_reif_cond);

    if (cond_lit)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(*cond_lit));

    print(s, " (");
    auto & first = _vars_swapped ? _vars_2 : _vars_1;
    auto & second = _vars_swapped ? _vars_1 : _vars_2;
    for (const auto & var : first)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") (");
    for (const auto & var : second)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ")");

    return s.str();
}
