#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_LINEAR_STAGES_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_LINEAR_STAGES_HH

#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/linear/justify.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/expression.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/reason.hh>
#include <gcs/variable_condition.hh>

#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief One linear (in)equality piece of a fused constraint's propagator:
     * the tidied terms, the target value (tidying modifier folded in), whether
     * it is an equality, its OPB lines, and an optional gating condition. The
     * gate is also the extra reason literal, and the emitted OPB line is
     * half-reified on it.
     *
     * A compound constraint that emits one flat OPB block (issue #448) builds
     * a list of these with add_equality_stage() / add_le_stage(), and its
     * propagator runs them with propagate_stages().
     *
     * \ingroup Innards
     */
    struct LinearStage
    {
        TidiedUpLinear terms;
        Integer value;
        bool equality;
        std::pair<std::optional<ProofLine>, std::optional<ProofLine>> lines;
        std::optional<IntegerVariableCondition> gate;
    };

    /**
     * \brief Is a stage's gating condition currently established? Only the
     * operators the fused constraints gate on are supported.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto stage_gate_holds(const State & state, const IntegerVariableCondition & cond) -> bool;

    /**
     * \brief Append an ungated equality stage, emitting its OPB lines
     * `@c[label][<role>le]` / `@c[label][<role>ge]` when model is non-null.
     *
     * \ingroup Innards
     */
    auto add_equality_stage(std::vector<LinearStage> & stages, ProofModel * const model, const ConstraintID & id, const WeightedSum & sum,
        Integer value, const std::string & role) -> void;

    /**
     * \brief Append a less-than-or-equal stage, emitting its OPB line
     * `@c[label][<role>]` when model is non-null, half-reified on the gate if
     * one is given.
     *
     * \ingroup Innards
     */
    auto add_le_stage(std::vector<LinearStage> & stages, ProofModel * const model, const ConstraintID & id, const WeightedSum & sum, Integer value,
        const std::string & role, const std::optional<IntegerVariableCondition> & gate) -> void;

    /**
     * \brief Run each currently-active stage once through propagate_linear.
     * Returns false if a stage hit a contradiction on the tracker's
     * non-throwing failure path, in which case the caller must stop rather
     * than run anything further on an emptied domain.
     *
     * \ingroup Innards
     */
    auto propagate_stages(const std::vector<LinearStage> & stages, const State & state, auto & inference, ProofLogger * const logger,
        const ConstraintID & owner) -> bool
    {
        for (const auto & stage : stages) {
            if (stage.gate && ! stage_gate_holds(state, *stage.gate)) {
                // Contrapositive: if the gated inequality is already violated
                // in bounds, the gate cannot hold. (Gated stages are always
                // inequalities.) The justification must materialise the sum of
                // the half-reified stage line and the term bounds explicitly:
                // reverse unit propagation cannot combine them on its own.
                if (! stage.equality) {
                    visit(
                        [&](const auto & cv) {
                            Integer smallest_sum = 0_i;
                            ReasonLiterals reason;
                            LinearBounds bounds;
                            for (const auto & term : cv.terms) {
                                auto var = get_var(term);
                                auto coeff = get_coeff(term);
                                auto [lo, hi] = state.bounds(var);
                                bounds.emplace_back(lo, hi);
                                if (coeff >= 0_i) {
                                    smallest_sum += coeff * lo;
                                    reason.emplace_back(var >= lo);
                                }
                                else {
                                    smallest_sum += coeff * hi;
                                    reason.emplace_back(var <= hi);
                                }
                            }
                            if (smallest_sum > stage.value) {
                                auto justf = [&](const ReasonLiterals &) {
                                    justify_linear_contrapositive(*logger, cv, bounds, stage.lines.first.value());
                                };
                                inference.infer(logger, ! Literal{*stage.gate}, JustifyExplicitly{justf, ThenRUP::Yes, hints::LinearEquality{owner}},
                                    ExplicitReason{std::move(reason)});
                            }
                        },
                        stage.terms);
                    if (inference.contradicted())
                        return false;
                }
                continue;
            }
            visit(
                [&](const auto & cv) {
                    propagate_linear(cv, stage.value, state, inference, logger, stage.equality, stage.lines,
                        stage.gate ? std::optional<Literal>{*stage.gate} : std::nullopt, hints::LinearEquality{owner});
                },
                stage.terms);
            if (inference.contradicted())
                return false;
        }
        return true;
    }
}

#endif
