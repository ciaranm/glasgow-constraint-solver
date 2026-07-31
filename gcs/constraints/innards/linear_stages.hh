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
     * A compound constraint that emits one flat OPB block (issue #448) decides on
     * a list of StageSpecs, has define_proof_model() emit their rows and
     * install_propagators() turn them into these, and its propagator runs them
     * with propagate_stages().
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
     * \brief One stage as decided on, before its OPB rows exist: the untidied sum
     * and value the rows state, the role naming them, and the gate they are
     * half-reified on.
     *
     * The rows and the LinearStage are wanted in different install phases -- the
     * rows only with proofs on, the stage always -- so a constraint decides on
     * these in prepare(), emits the rows from define_proof_model() with
     * emit_stage_rows(), and builds the stages from make_stages() in
     * install_propagators().
     *
     * \ingroup Innards
     */
    struct StageSpec
    {
        WeightedSum sum;
        Integer value;
        bool equality;
        std::string role;
        std::optional<IntegerVariableCondition> gate;
        /// Filled in by emit_stage_rows(); empty with proofs off.
        std::pair<std::optional<ProofLine>, std::optional<ProofLine>> lines{};
    };

    /**
     * \brief Is a stage's gating condition currently established? Only the
     * operators the fused constraints gate on are supported.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto stage_gate_holds(const State & state, const IntegerVariableCondition & cond) -> bool;

    /// Decide on an ungated equality stage, whose rows are `@c[label][<role>le]` / `@c[label][<role>ge]`.
    auto add_equality_stage(std::vector<StageSpec> & specs, const WeightedSum & sum, Integer value, const std::string & role) -> void;

    /// Decide on a less-than-or-equal stage, whose row is `@c[label][<role>]`, half-reified on the gate if one is given.
    auto add_le_stage(std::vector<StageSpec> & specs, const WeightedSum & sum, Integer value, const std::string & role,
        const std::optional<IntegerVariableCondition> & gate) -> void;

    /**
     * \brief Emit every spec's OPB rows, in order, keeping the line handles on the
     * specs. define_proof_model()'s half.
     *
     * \ingroup Innards
     */
    auto emit_stage_rows(ProofModel & model, const ConstraintID & id, std::vector<StageSpec> & specs) -> void;

    /**
     * \brief Turn the specs into the propagator's stages, citing whatever rows
     * emit_stage_rows() left on them. install_propagators()'s half.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto make_stages(const std::vector<StageSpec> & specs) -> std::vector<LinearStage>;

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
