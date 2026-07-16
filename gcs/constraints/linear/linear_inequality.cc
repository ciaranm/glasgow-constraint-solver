#include <gcs/constraints/innards/reified_dispatcher.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/linear/linear_inequality.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <memory>
#include <optional>
#include <sstream>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_pair;
using std::make_shared;
using std::nullopt;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::variant;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

ReifiedLinearInequality::ReifiedLinearInequality(
    WeightedSum coeff_vars, Integer value, ReificationCondition cond, std::optional<std::size_t> incremental_threshold) :
    _coeff_vars(move(coeff_vars)), _value(value), _reif_cond(cond), _incremental_threshold(incremental_threshold)
{
}

auto ReifiedLinearInequality::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ReifiedLinearInequality>(WeightedSum{_coeff_vars}, _value, _reif_cond, _incremental_threshold);
}

namespace
{
    auto justify_cond(const State & state, const auto & coeff_vars, ProofLogger & logger,
        const pair<optional<ProofLine>, optional<ProofLine>> & proof_lines) -> void
    {
        // Deview mode: see justify_linear_bounds for the rationale.
        PolBuilder pol;
        pol.enable_deview_mode(logger.names_and_ids_tracker());
        pol.add(proof_lines.first.value());

        for (const auto & cv : coeff_vars.terms) {
            // the following line of logic is definitely correct until you inevitably
            // discover otherwise
            bool upper = (get_coeff(cv) < 0_i);
            auto lit = upper ? get_var(cv) <= state.upper_bound(get_var(cv)) : get_var(cv) >= state.lower_bound(get_var(cv));
            pol.add_for_literal(logger.names_and_ids_tracker(), lit, abs(get_coeff(cv)));
        }

        pol.emit(logger, ProofLevel::Temporary);
    }
}

namespace gcs::innards::hints
{
    template <typename CoeffVars_>
    auto emit_justification(ProofLogger & logger, const LinearInequalityCond<CoeffVars_> & w, const ReasonLiterals &) -> void
    {
        justify_cond(*w.state, w.coeff_vars, logger, w.proof_lines);
    }
}

auto ReifiedLinearInequality::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators, initial_state);
}

auto ReifiedLinearInequality::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _evaluated_cond = test_reification_condition(initial_state, _reif_cond);
    return true;
}

auto ReifiedLinearInequality::define_proof_model(ProofModel & model) -> void
{
    WPBSum terms;
    for (auto & [c, v] : _coeff_vars.terms)
        terms += c * v;

    overloaded{
        [&](const reif::MustHold &) {
            // cake_pb_cp labels the unconditional inequality @c[<id>] (no role).
            _proof_lines = pair{model.add_labelled_constraint(constraint_id(), "", terms <= _value), nullopt};
        }, //
        [&](const reif::MustNotHold &) {
            _proof_lines = pair{model.add_labelled_constraint(constraint_id(), "", terms >= _value + 1_i), nullopt};
        }, //
        [&](const reif::If & cond) {
            // cake_pb_cp labels the half-reified inequality @c[<id>], with no role
            // suffix, exactly like the unconditional form.
            _proof_lines = pair{model.add_labelled_constraint(constraint_id(), "", terms <= _value, HalfReifyOnConjunctionOf{cond.cond}), nullopt};
        }, //
        [&](const reif::NotIf & cond) {
            // s_expr throws on NotIf, so this form never reaches the cake chain and
            // the invented role is fine.
            _proof_lines = pair{model.add_labelled_constraint(constraint_id(), "ltn", terms <= _value, HalfReifyOnConjunctionOf{cond.cond}), nullopt};
        }, //
        [&](const reif::Iff & cond) {
            // cake_pb_cp labels the iff halves r (cond -> ineq) and f (~cond -> its
            // integer negation).
            _proof_lines = pair{model.add_labelled_constraint(constraint_id(), "r", terms <= _value, HalfReifyOnConjunctionOf{cond.cond}),
                model.add_labelled_constraint(constraint_id(), "f", terms >= _value + 1_i, HalfReifyOnConjunctionOf{! cond.cond})};
        } //
    }
        .visit(_reif_cond);
}

auto ReifiedLinearInequality::install_propagators(Propagators & propagators, State & initial_state) -> void
{
    auto proof_lines = _proof_lines;
    auto proof_lines_swapped = pair{_proof_lines.second, _proof_lines.first};

    auto [sanitised_cv, modifier] = tidy_up_linear(_coeff_vars);

    auto neg_coeff_vars = _coeff_vars;
    for (auto & v : neg_coeff_vars.terms)
        v.coefficient = -v.coefficient;
    auto [sanitised_neg_cv, neg_modifier] = tidy_up_linear(neg_coeff_vars);

    vector<IntegerVariableID> vars;
    visit(
        [&](const auto & sanitised_cv) {
            for (const auto & cv : sanitised_cv.terms)
                vars.push_back(get_var(cv));
        },
        sanitised_cv);

    // Trigger on the sanitised terms, not the user's: tidy_up_linear coalesces
    // repeats and resolves views (2a + 3a -> 5a), and these deduplicated
    // underlying variables are the propagator's actual read/write scope. The
    // user's raw terms would register a repeated variable twice and spuriously
    // trip the idempotence-claim downgrade.
    Triggers triggers;
    for (const auto & v : vars)
        triggers.on_bounds.push_back(v);

    visit(
        [&, modifier = modifier, neg_modifier = neg_modifier](const auto & sanitised_cv, const auto & sanitised_neg_cv) -> void {
            // The verdict justification is the linear "cond forced" witness over the
            // sanitised coeff-vector type (and its negation for the must-hold side); a
            // variant of the two, collapsing to a single witness when the two deduced
            // types coincide.
            using CV = std::decay_t<decltype(sanitised_cv)>;
            using NegCV = std::decay_t<decltype(sanitised_neg_cv)>;
            using LinearCondJustification = std::conditional_t<std::is_same_v<CV, NegCV>, JustifyExplicitly<hints::LinearInequalityCond<CV>>,
                std::variant<JustifyExplicitly<hints::LinearInequalityCond<CV>>, JustifyExplicitly<hints::LinearInequalityCond<NegCV>>>>;

            // Each enforce direction always re-runs the same single propagation while its
            // verdict holds (the dispatcher keeps it Enabled within a subtree where the
            // condition is decided one way), so each can fold its own fixed terms away
            // incrementally. The two directions need independent fold states: within any
            // one subtree only one direction runs, and each state backtracks on its own
            // ConstraintStateHandle, so an under-folded state (vars instantiated while the
            // other direction was active) is still correct -- it just re-folds them on its
            // next run. Set up a state only for a direction the dispatcher can actually
            // reach: must-hold for everything but an unconditional must-not-hold; must-not-
            // hold only for an unconditional must-not-hold or a full Iff (a half-reified
            // If/NotIf deactivates rather than enforcing the negation).
            const auto threshold = _incremental_threshold.value_or(default_linear_incremental_threshold());
            const bool und = std::holds_alternative<evaluated_reif::Undecided>(_evaluated_cond);
            const bool may_must_hold = std::holds_alternative<evaluated_reif::MustHold>(_evaluated_cond) || und;
            const bool may_must_not_hold =
                std::holds_alternative<evaluated_reif::MustNotHold>(_evaluated_cond) || (und && std::holds_alternative<reif::Iff>(_reif_cond));

            auto setup_inc = [&](const auto & cv) -> std::pair<std::shared_ptr<std::vector<std::size_t>>, ConstraintStateHandle> {
                auto active = make_shared<std::vector<std::size_t>>(cv.terms.size());
                for (std::size_t i = 0; i != cv.terms.size(); ++i)
                    (*active)[i] = i;
                auto handle = initial_state.add_constraint_state(LinearIncrementalState{cv.terms.size(), 0_i});
                return std::pair{active, handle};
            };

            std::optional<std::pair<std::shared_ptr<std::vector<std::size_t>>, ConstraintStateHandle>> inc_must_hold, inc_must_not_hold;
            if (may_must_hold && sanitised_cv.terms.size() >= threshold)
                inc_must_hold = setup_inc(sanitised_cv);
            if (may_must_not_hold && sanitised_neg_cv.terms.size() >= threshold)
                inc_must_not_hold = setup_inc(sanitised_neg_cv);

            auto enforce_constraint_must_hold = [sanitised_cv, value = _value, modifier = modifier, proof_lines, inc_must_hold](const State & state,
                                                    auto & inference, ProofLogger * const logger, const Literal & cond) -> PropagatorState {
                if (inc_must_hold)
                    return propagate_linear_incremental(sanitised_cv, value + modifier, state, inference, logger, false, proof_lines, cond,
                        *inc_must_hold->first, inc_must_hold->second);
                return propagate_linear(sanitised_cv, value + modifier, state, inference, logger, false, proof_lines, cond);
            };

            auto enforce_constraint_must_not_hold = [sanitised_neg_cv, value = _value, neg_modifier = neg_modifier, proof_lines_swapped,
                                                        inc_must_not_hold](const State & state, auto & inference, ProofLogger * const logger,
                                                        const Literal & cond) -> PropagatorState {
                if (inc_must_not_hold)
                    return propagate_linear_incremental(sanitised_neg_cv, -value + neg_modifier - 1_i, state, inference, logger, false,
                        proof_lines_swapped, cond, *inc_must_not_hold->first, inc_must_not_hold->second);
                return propagate_linear(sanitised_neg_cv, -value + neg_modifier - 1_i, state, inference, logger, false, proof_lines_swapped, cond);
            };

            // Whole-scope reason built once (capture-init) and reused, not
            // rebuilt per verdict (see dev_docs/propagator-performance.md).
            auto infer_cond_when_undecided = [sanitised_cv, sanitised_neg_cv, value = _value, modifier = modifier, proof_lines, proof_lines_swapped,
                                                 reason = generic_reason(vars),
                                                 owner = constraint_id()](const State & state, auto &, ProofLogger * const,
                                                 const IntegerVariableCondition &) -> ReificationVerdictFor<LinearCondJustification> {
                Integer min_possible = 0_i, max_possible = 0_i;
                for (const auto & cv : sanitised_cv.terms) {
                    auto bounds = state.bounds(get_var(cv));
                    if (get_coeff(cv) >= 0_i) {
                        min_possible += get_coeff(cv) * bounds.first;
                        max_possible += get_coeff(cv) * bounds.second;
                    }
                    else {
                        min_possible += get_coeff(cv) * bounds.second;
                        max_possible += get_coeff(cv) * bounds.first;
                    }
                }

                if (min_possible > value + modifier) {
                    // cannot possibly hold
                    return reification_verdict::MustNotHold<LinearCondJustification>{
                        .justification =
                            JustifyExplicitly{hints::LinearInequalityCond<CV>{{owner}, &state, sanitised_cv, proof_lines}, ThenRUP::Yes}, //
                        .reason = reason                                                                                                  //
                    };
                }
                else if (max_possible <= value + modifier) {
                    // must definitely hold
                    return reification_verdict::MustHold<LinearCondJustification>{
                        .justification = JustifyExplicitly{hints::LinearInequalityCond<NegCV>{{owner}, &state, sanitised_neg_cv, proof_lines_swapped},
                            ThenRUP::Yes}, //
                        .reason = reason   //
                    };
                }
                else
                    return reification_verdict::StillUndecided{};
            };

            // Slack-based waking: for a direction that is decided at install time
            // (an unconditional inequality, or a half-reified one already fixed) and
            // is long enough and loose enough that most coarse wakes cannot propagate,
            // wake via refined watches on a covering subset of the terms instead of on
            // every bound of every term. Only the wake condition changes -- the sweep,
            // its inferences, and its proof are exactly the coarse propagator's -- so
            // bypass the dispatcher for that single direction and run the sweep
            // directly, re-arming the covering set after each clean wake. The
            // genuinely-undecided reified case (and equality) keep the coarse path.
            const auto slack_threshold = default_linear_slack_watch_threshold();
            const auto slack_cover_percent = default_linear_slack_watch_cover_percent();
            auto want_slack = [&](const auto & cv, Integer val) -> bool {
                const auto len = cv.terms.size();
                if (len < slack_threshold)
                    return false;
                return linear_slack_cover_size(cv, val, initial_state) * 100 <= slack_cover_percent * len;
            };
            auto install_slack_watched = [&](const auto & cv, Integer val, const Literal & cond, const auto & dir_proof_lines) {
                Triggers slack_triggers;
                for (const auto & term : cv.terms)
                    slack_triggers.scope_only.push_back(get_var(term));
                propagators.install(
                    constraint_id(),
                    [cv, val, cond, dir_proof_lines](
                        const State & state, auto & inference, ProofLogger * const logger, const RefinedWatchContext & ctx) -> PropagatorState {
                        auto r = propagate_linear(cv, val, state, inference, logger, false, dir_proof_lines, cond);
                        // Re-arm only after a clean sweep; on a contradiction the state
                        // is not safe to read again. scope_only means no coarse re-wake,
                        // so return Enable to stay wakeable by the watches.
                        if (r == PropagatorState::EnableButIdempotent)
                            rearm_linear_slack_watches(cv, val, state, ctx);
                        return PropagatorState::Enable;
                    },
                    std::move(slack_triggers));
            };

            if (auto mh = std::get_if<evaluated_reif::MustHold>(&_evaluated_cond); mh && want_slack(sanitised_cv, _value + modifier)) {
                install_slack_watched(sanitised_cv, _value + modifier, mh->cond, proof_lines);
                return;
            }
            if (auto mnh = std::get_if<evaluated_reif::MustNotHold>(&_evaluated_cond);
                mnh && want_slack(sanitised_neg_cv, -_value + neg_modifier - 1_i)) {
                install_slack_watched(sanitised_neg_cv, -_value + neg_modifier - 1_i, mnh->cond, proof_lines_swapped);
                return;
            }

            install_reified_dispatcher(propagators, constraint_id(), _evaluated_cond, _reif_cond, triggers, std::move(enforce_constraint_must_hold),
                std::move(enforce_constraint_must_not_hold), std::move(infer_cond_when_undecided));
        },
        sanitised_cv, sanitised_neg_cv);
}

// cake_pb_cp's name for the <= form is lin_less_equal (not lin_less_than_equal).
auto ReifiedLinearInequality::constraint_type() const -> std::string
{
    return "lin_less_equal";
}

auto ReifiedLinearInequality::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    auto [rei, suffix] = overloaded{
        [&](const reif::MustHold &) { return make_pair(false, ""); }, //
        [&](const reif::If &) { return make_pair(true, "_if"); },     //
        [&](const reif::Iff &) { return make_pair(true, "_iff"); },   //
        [&](const auto &) {
            throw UnexpectedException{"Unexpected reification type in s_expr"};
            return make_pair(false, "");
        } //
    }
                             .visit(_reif_cond);

    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type() + suffix)};
    if (rei)
        terms.push_back(*tracker.s_expr_term_of(_reif_cond));

    vector<SExpr> coeff_vars;
    for (const auto & [c, v] : _coeff_vars.terms) {
        coeff_vars.push_back(SExpr::atom(c.to_string()));
        coeff_vars.push_back(tracker.s_expr_term_of(v));
    }
    terms.push_back(SExpr::list(std::move(coeff_vars)));
    terms.push_back(SExpr::atom(_value.to_string()));

    return SExpr::list(std::move(terms));
}
