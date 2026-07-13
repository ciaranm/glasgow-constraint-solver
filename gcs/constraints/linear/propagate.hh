#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_PROPAGATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_PROPAGATE_HH

#include <gcs/constraints/linear/utils.hh>
#include <gcs/expression.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state.hh>

#include <cstddef>
#include <optional>
#include <vector>

namespace gcs::innards
{
    class RefinedWatchContext;

    /**
     * \brief Propagate a linear equality or inequality.
     *
     * \ingroup Innards
     */
    template <typename Hint_ = NoHint>
    auto propagate_linear(const auto & terms, Integer, const State &, auto & inference_tracker, ProofLogger * const logger, bool equality,
        const std::optional<std::pair<std::optional<ProofLine>, std::optional<ProofLine>>> & proof_line, const std::optional<Literal> & add_to_reason,
        const Hint_ & hint = {}) -> PropagatorState;

    /**
     * \brief Recompute and re-arm a linear inequality's slack-covering watch set.
     *
     * For `Sum(coeff_i x_i) <= value`, after the forward sweep has reached its
     * fixpoint: watch a covering subset of the terms so that no *un*watched term's
     * remaining movement can, even cumulatively, drop the slack enough to enable a
     * propagation. Each term's potential is `|coeff_i| * (ub_i - lb_i)` -- the most
     * it can still raise the lower sum; at the fixpoint every potential is `<=
     * slack`, so with `margin = slack - max_potential (>= 0)` we watch from the
     * largest potential downwards until the unwatched potentials sum to within the
     * margin. Only a watched term's min-contribution bound moving (the lower bound
     * of a positive-coefficient term, the upper bound of a negative one) can then
     * matter, so that is exactly the literal watched. Clears the propagator's
     * existing watches first, so a term that has left the covering set is dropped.
     *
     * Only the wake condition changes: the inferences (hence the search tree and
     * the proof) are exactly those of the coarse propagator woken only when a
     * covering term moves. Call only after a clean sweep (state must be readable).
     *
     * \ingroup Innards
     */
    template <typename CoeffVars_>
    auto rearm_linear_slack_watches(const CoeffVars_ & coeff_vars, Integer value, const State & state, const RefinedWatchContext & ctx) -> void;

    /**
     * \brief The number of terms `rearm_linear_slack_watches` would watch for
     * `Sum(coeff_i x_i) <= value` at the given state -- the size of the covering
     * set. Used at install time to decide whether slack-based waking is worthwhile:
     * a small covering set (few large-potential terms dominating, as happens with
     * heavily mismatched coefficients or a loose bound) means most wakes are wasted,
     * so watching pays off; a covering set near the full length does not.
     *
     * \ingroup Innards
     */
    template <typename CoeffVars_>
    [[nodiscard]] auto linear_slack_cover_size(const CoeffVars_ & coeff_vars, Integer value, const State & state) -> std::size_t;

    /**
     * \brief The default minimum number of terms below which slack-based waking is
     * never used for a linear inequality (the covering set's overhead is not worth
     * it on a short constraint, where the coarse or incremental sweep is cheap).
     * Overridable via GCS_LINEAR_SLACK_WATCH_THRESHOLD; a huge value disables
     * slack-waking entirely.
     */
    [[nodiscard]] auto default_linear_slack_watch_threshold() -> std::size_t;

    /**
     * \brief The default maximum covering-set size, as a percentage of the term
     * count, for slack-based waking to be used: above it the wake reduction is too
     * small to pay for the per-wake re-arm. Overridable via
     * GCS_LINEAR_SLACK_WATCH_COVER_PERCENT.
     */
    [[nodiscard]] auto default_linear_slack_watch_cover_percent() -> std::size_t;

    /**
     * \brief Backtrackable state for the incremental linear propagator: the count of
     * not-yet-instantiated ("active") terms, and the summed contribution of the
     * instantiated ("fixed") ones (a fixed term contributes coeff*value to the lower
     * sum, and -coeff*value to the inverse/upper sum).
     *
     * \ingroup Innards
     */
    struct LinearIncrementalState
    {
        std::size_t n_active;
        Integer fixed_lower;
    };

    /**
     * \brief The default minimum number of terms at and above which a linear
     * (in)equality uses the incremental propagator, used when a constraint is posted
     * without an explicit threshold. A wide threshold keeps narrow constraints on the
     * cheaper stateless path, where the incremental bookkeeping does not pay off.
     *
     * The per-constraint threshold (a constructor argument on the linear constraints)
     * is the intended interface; this default is overridable via the
     * GCS_LINEAR_INCREMENTAL_THRESHOLD environment variable, which is how the test
     * suite sweeps both code paths (threshold 0 = always incremental, a huge value =
     * always stateless).
     */
    [[nodiscard]] auto default_linear_incremental_threshold() -> std::size_t;

    /**
     * \brief Incremental variant of propagate_linear: folds instantiated terms out of
     * the active set so each firing only walks the still-unassigned terms. `active`
     * is a persistent (non-backtracked) permutation of term indices, mutated in place;
     * `state_handle` refers to a LinearIncrementalState added via add_constraint_state.
     *
     * \ingroup Innards
     */
    template <typename Hint_ = NoHint>
    auto propagate_linear_incremental(const auto & terms, Integer, const State &, auto & inference_tracker, ProofLogger * const logger, bool equality,
        const std::optional<std::pair<std::optional<ProofLine>, std::optional<ProofLine>>> & proof_line, const std::optional<Literal> & add_to_reason,
        std::vector<std::size_t> & active, ConstraintStateHandle state_handle, const Hint_ & hint = {}) -> PropagatorState;

    /**
     * \brief Propagate a not-equals
     *
     * \ingroup Innards
     */
    template <typename Hint_ = NoHint>
    auto propagate_linear_not_equals(const auto & terms, Integer, const State &, auto & inference_tracker, ProofLogger * const logger,
        const std::vector<IntegerVariableID> & all_vars_for_reason, const Hint_ & hint = {}) -> PropagatorState;
}

#endif
