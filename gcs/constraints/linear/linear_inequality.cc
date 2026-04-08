#include <gcs/constraints/linear/linear_inequality.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <sstream>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::variant;
using std::vector;

ReifiedLinearInequality::ReifiedLinearInequality(WeightedSum coeff_vars, Integer value, ReificationCondition cond) :
    _coeff_vars(move(coeff_vars)),
    _value(value),
    _reif_cond(cond)
{
}

auto ReifiedLinearInequality::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ReifiedLinearInequality>(WeightedSum{_coeff_vars}, _value, _reif_cond);
}

namespace
{
    auto justify_cond(const State & state, const auto & coeff_vars, ProofLogger & logger,
        const ProofLine & proof_line) -> void
    {
        vector<pair<Integer, variant<ProofLine, XLiteral>>> terms_to_sum;
        terms_to_sum.emplace_back(1_i, proof_line);

        for (const auto & cv : coeff_vars.terms) {
            // the following line of logic is definitely correct until you inevitably
            // discover otherwise
            bool upper = (get_coeff(cv) < 0_i);

            auto literal_defining_proof_line = logger.names_and_ids_tracker().need_pol_item_defining_literal(
                upper ? get_var(cv) < state.upper_bound(get_var(cv) + 1_i) : get_var(cv) >= state.lower_bound(get_var(cv)));

            terms_to_sum.emplace_back(abs(get_coeff(cv)), literal_defining_proof_line);
        }

        stringstream step;
        step << "pol";
        bool first = true;
        for (auto & c_and_l : terms_to_sum) {
            overloaded{
                [&](const XLiteral & l) {
                    if (c_and_l.first == 1_i)
                        step << " " << logger.names_and_ids_tracker().pb_file_string_for(l);
                    else
                        step << " " << logger.names_and_ids_tracker().pb_file_string_for(l) << " " << c_and_l.first << " *";
                },
                [&](const ProofLine & l) {
                    if (c_and_l.first == 1_i)
                        step << " " << l;
                    else
                        step << " " << l << " " << c_and_l.first << " *";
                }}
                .visit(c_and_l.second);
            if (! first)
                step << " +";
            first = false;
        }
        step << ';';
        logger.emit_proof_line(step.str(), ProofLevel::Temporary);
    }
}

auto ReifiedLinearInequality::install(Propagators & propagators, State & state, ProofModel * const optional_model) && -> void
{
    optional<ProofLine> proof_line;
    if (optional_model) {
        WPBSum terms;
        for (auto & [c, v] : _coeff_vars.terms)
            terms += c * v;

        overloaded{
            [&](const reif::MustHold &) {
                proof_line = optional_model->add_constraint("ReifiedLinearInequality", "unconditional less than", terms <= _value, nullopt);
            },
            [&](const reif::MustNotHold &) {
                proof_line = optional_model->add_constraint("ReifiedLinearInequality", "unconditional greater than", terms >= _value + 1_i, nullopt);
            },
            [&](const reif::If & cond) {
                proof_line = optional_model->add_constraint("ReifiedLinearInequality", "less than option", terms <= _value, HalfReifyOnConjunctionOf{cond.cond});
            },
            [&](const reif::NotIf & cond) {
                proof_line = optional_model->add_constraint("ReifiedLinearInequality", "greater than option", terms <= _value, HalfReifyOnConjunctionOf{cond.cond});
            },
            [&](const reif::Iff & cond) {
                proof_line = optional_model->add_constraint("ReifiedLinearInequality", "less than option", terms <= _value, HalfReifyOnConjunctionOf{cond.cond});
                optional_model->add_constraint("ReifiedLinearInequality", "greater than option", terms >= _value + 1_i, HalfReifyOnConjunctionOf{! cond.cond});
            }}
            .visit(_reif_cond);
    }

    auto [sanitised_cv, modifier] = tidy_up_linear(_coeff_vars);

    overloaded{
        [&](const evaluated_reif::MustHold & reif) {
            // definitely true, it's a less-than-or-equal, which triggers on bounds changes only
            Triggers triggers;
            for (auto & [_, v] : _coeff_vars.terms)
                triggers.on_bounds.push_back(v);

            visit(
                [&, modifier = modifier](const auto & lin) {
                    propagators.install([modifier = modifier, lin = lin, value = _value, cond = reif.cond, proof_line = proof_line](
                                            const State & state, auto & inference, ProofLogger * const logger) {
                        return propagate_linear(lin, value + modifier, state, inference, logger, false, proof_line, cond);
                    },
                        triggers, "linear inequality");
                },
                sanitised_cv);
        },

        [&](const evaluated_reif::MustNotHold & reif) {
            // definitely false, it's a greater-than
            Triggers triggers;
            for (auto & [_, v] : _coeff_vars.terms)
                triggers.on_bounds.push_back(v);

            auto neg_coeff_vars = _coeff_vars;
            for (auto & v : neg_coeff_vars.terms)
                v.coefficient = -v.coefficient;
            auto [sanitised_neg_cv, neg_modifier] = tidy_up_linear(neg_coeff_vars);
            visit(
                [&, neg_modifier = neg_modifier](const auto & lin) {
                    propagators.install([neg_modifier = neg_modifier, lin = lin, value = -_value - 1_i, inv_cond = reif.cond ? *reif.cond : reif.cond, proof_line = proof_line](
                                            const State & state, auto & inference, ProofLogger * const logger) {
                        return propagate_linear(lin, value + neg_modifier, state, inference, logger, false, *proof_line + 1, inv_cond);
                    },
                        triggers, "linear inequality");
                },
                sanitised_neg_cv);
        },

        [&](const evaluated_reif::Deactivated &) {
            // doesn't do anything
        },

        [&](const evaluated_reif::Undecided & reif) {
            // condition wasn't known at compile time. keep both the satisfiable and unsatisfiable
            // forms of the inequality around, and then see if the condition is known or can be
            // inferred.

            Triggers triggers;
            for (auto & [_, v] : _coeff_vars.terms)
                triggers.on_bounds.push_back(v);
            triggers.on_change.push_back(reif.cond.var);

            auto neg_coeff_vars = _coeff_vars;
            for (auto & v : neg_coeff_vars.terms)
                v.coefficient = -v.coefficient;
            auto [sanitised_neg_cv, neg_modifier] = tidy_up_linear(neg_coeff_vars);

            vector<IntegerVariableID> vars;
            visit([&](const auto & sanitised_cv) {
                for (const auto & cv : sanitised_cv.terms)
                    vars.push_back(get_var(cv));
            },
                sanitised_cv);

            visit([&, modifier = modifier, neg_modifier = neg_modifier](const auto & sanitised_cv, const auto & sanitised_neg_cv) -> void {
                propagators.install([cond = _reif_cond, sanitised_cv = sanitised_cv, sanitised_neg_cv = sanitised_neg_cv,
                                        value = _value, modifier = modifier, neg_modifier = neg_modifier, proof_line = proof_line,
                                        vars = vars](
                                        const State & state, auto & inference, ProofLogger * const logger) {
                    return overloaded{
                        [&](const evaluated_reif::MustHold & reif) {
                            return propagate_linear(sanitised_cv, value + modifier, state, inference, logger, false, proof_line, reif.cond);
                        },

                        [&](const evaluated_reif::MustNotHold & reif) {
                            return propagate_linear(sanitised_neg_cv, -value + neg_modifier - 1_i, state, inference, logger, false, *proof_line + 1, reif.cond ? *reif.cond : reif.cond);
                        },

                        [&](const evaluated_reif::Deactivated &) {
                            return PropagatorState::DisableUntilBacktrack;
                        },

                        [&](const evaluated_reif::Undecided & reif) {
                            // still don't know. see whether the condition is forced either way.
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
                                auto just = [&](const ReasonFunction &) { return justify_cond(state, sanitised_cv, *logger, *proof_line); };
                                if (reif.set_not_cond_if_must_not_hold)
                                    inference.infer(logger, ! reif.cond, JustifyExplicitly{just}, generic_reason(state, vars));
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else if (max_possible <= value + modifier) {
                                // must definitely hold
                                auto just = [&](const ReasonFunction &) { return justify_cond(state, sanitised_neg_cv, *logger, *proof_line + 1); };
                                if (reif.set_cond_if_must_hold)
                                    inference.infer(logger, reif.cond, JustifyExplicitly{just}, generic_reason(state, vars));
                                else if (reif.set_not_cond_if_must_hold)
                                    inference.infer(logger, ! reif.cond, JustifyExplicitly{just}, generic_reason(state, vars));
                                return PropagatorState::DisableUntilBacktrack;
                            }
                            else {
                                // still unknown
                                return PropagatorState::Enable;
                            }
                        }}
                        .visit(state.test_reification_condition(cond));
                },
                    triggers, "linear inequality");
            },
                sanitised_cv, sanitised_neg_cv);
        }}
        .visit(state.test_reification_condition(_reif_cond));
}
