#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH 1

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/expression.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/reification.hh>

#include <cstddef>
#include <memory>
#include <optional>
#include <utility>

namespace gcs
{
    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is less than or equal to the specified
     * value, if and possibly only if the condition holds.
     *
     * \ingroup innards
     * \sa LinearLessThanEqual
     * \sa LinearGreaterThanEqual
     */
    class ReifiedLinearInequality : public Constraint
    {
    private:
        WeightedSum _coeff_vars;
        Integer _value;
        ReificationCondition _reif_cond;
        std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>> _proof_lines;
        innards::EvaluatedReificationCondition _evaluated_cond = innards::evaluated_reif::Deactivated{};
        // Per-constraint width at/above which to use the incremental propagator; unset
        // means use innards::default_linear_incremental_threshold().
        std::optional<std::size_t> _incremental_threshold;

        // tidy_up_linear() of _coeff_vars and of its negation, computed once in
        // prepare(), because the decisions below and install_propagators() all need
        // them.
        innards::TidiedUpLinear _sanitised, _sanitised_neg;
        Integer _modifier = 0_i, _neg_modifier = 0_i;

        // The two directions' backtrackable fold states, allocated in prepare() and
        // consumed by install_propagators(). Each is set only for a direction the
        // dispatcher can actually reach and that is wide enough to pay for folding:
        // every constraint-state slot is deep-copied at every search node, so one
        // allocated for an unreachable direction is a real cost.
        std::optional<innards::ConstraintStateHandle> _incremental_must_hold, _incremental_must_not_hold;

        // Whether a direction is decided at install time and loose enough to wake on
        // slack watches rather than on every bound of every term. Deciding needs the
        // initial domains (linear_slack_cover_size sizes the covering set against
        // them), so it happens in prepare().
        bool _slack_watch_must_hold = false, _slack_watch_must_not_hold = false;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit ReifiedLinearInequality(
            WeightedSum coeff_vars, Integer value, ReificationCondition cond, std::optional<std::size_t> incremental_threshold = std::nullopt);

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
