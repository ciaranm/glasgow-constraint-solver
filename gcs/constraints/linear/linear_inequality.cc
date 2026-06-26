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

#include <sstream>

using namespace gcs;
using namespace gcs::innards;

using std::make_pair;
using std::nullopt;
using std::optional;
using std::pair;
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

ReifiedLinearInequality::ReifiedLinearInequality(WeightedSum coeff_vars, Integer value, ReificationCondition cond) :
    _coeff_vars(move(coeff_vars)), _value(value), _reif_cond(cond)
{
}

auto ReifiedLinearInequality::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ReifiedLinearInequality>(WeightedSum{_coeff_vars}, _value, _reif_cond);
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

    install_propagators(propagators);
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
            _proof_lines = pair{model.add_constraint("ReifiedLinearInequality", "unconditional less than", terms <= _value, nullopt), nullopt};
        }, //
        [&](const reif::MustNotHold &) {
            _proof_lines =
                pair{model.add_constraint("ReifiedLinearInequality", "unconditional greater than", terms >= _value + 1_i, nullopt), nullopt};
        }, //
        [&](const reif::If & cond) {
            _proof_lines = pair{
                model.add_constraint("ReifiedLinearInequality", "less than option", terms <= _value, HalfReifyOnConjunctionOf{cond.cond}), nullopt};
        }, //
        [&](const reif::NotIf & cond) {
            _proof_lines =
                pair{model.add_constraint("ReifiedLinearInequality", "greater than option", terms <= _value, HalfReifyOnConjunctionOf{cond.cond}),
                    nullopt};
        }, //
        [&](const reif::Iff & cond) {
            _proof_lines = pair{
                model.add_constraint("ReifiedLinearInequality", "less than option", terms <= _value, HalfReifyOnConjunctionOf{cond.cond}),
                model.add_constraint("ReifiedLinearInequality", "greater than option", terms >= _value + 1_i, HalfReifyOnConjunctionOf{! cond.cond})};
        } //
    }
        .visit(_reif_cond);
}

auto ReifiedLinearInequality::install_propagators(Propagators & propagators) -> void
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

    Triggers triggers;
    for (auto & [_, v] : _coeff_vars.terms)
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

            auto enforce_constraint_must_hold = [sanitised_cv, value = _value, modifier = modifier, proof_lines](const State & state,
                                                    auto & inference, ProofLogger * const logger, const Literal & cond) -> PropagatorState {
                return propagate_linear(sanitised_cv, value + modifier, state, inference, logger, false, proof_lines, cond);
            };

            auto enforce_constraint_must_not_hold = [sanitised_neg_cv, value = _value, neg_modifier = neg_modifier, proof_lines_swapped](
                                                        const State & state, auto & inference, ProofLogger * const logger,
                                                        const Literal & cond) -> PropagatorState {
                return propagate_linear(sanitised_neg_cv, -value + neg_modifier - 1_i, state, inference, logger, false, proof_lines_swapped, cond);
            };

            auto infer_cond_when_undecided = [sanitised_cv, sanitised_neg_cv, value = _value, modifier = modifier, proof_lines, proof_lines_swapped,
                                                 vars = vars, owner = constraint_id()](const State & state, auto &, ProofLogger * const,
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
                        .reason = generic_reason(vars)                                                                                    //
                    };
                }
                else if (max_possible <= value + modifier) {
                    // must definitely hold
                    return reification_verdict::MustHold<LinearCondJustification>{
                        .justification = JustifyExplicitly{hints::LinearInequalityCond<NegCV>{{owner}, &state, sanitised_neg_cv, proof_lines_swapped},
                            ThenRUP::Yes},             //
                        .reason = generic_reason(vars) //
                    };
                }
                else
                    return reification_verdict::StillUndecided{};
            };

            install_reified_dispatcher(propagators, constraint_id(), _evaluated_cond, _reif_cond, triggers, std::move(enforce_constraint_must_hold),
                std::move(enforce_constraint_must_not_hold), std::move(infer_cond_when_undecided));
        },
        sanitised_cv, sanitised_neg_cv);
}

auto ReifiedLinearInequality::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    // cake_pb_cp's name for the <= form is lin_less_equal (not lin_less_than_equal).
    auto [rei, cons] = overloaded{
        [&](const reif::MustHold &) { return make_pair(false, "lin_less_equal"); }, //
        [&](const reif::If &) { return make_pair(true, "lin_less_equal_if"); },     //
        [&](const reif::Iff &) { return make_pair(true, "lin_less_equal_iff"); },   //
        [&](const auto &) {
            throw UnexpectedException{"Unexpected reification type in s_expr"};
            return make_pair(false, "");
        } //
    }
                           .visit(_reif_cond);

    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(cons)};
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
