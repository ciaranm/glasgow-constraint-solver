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
