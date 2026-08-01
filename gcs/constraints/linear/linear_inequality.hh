#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH 1

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/expression.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/constraint_proof_model_data.hh>
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

        /**
         * \name Posted arguments, for presolvers.
         *
         * These read back the constraint exactly as it was constructed, so that
         * a presolver enumerating a Problem (see Problem::each_constraint_of_type)
         * can recognise a shape it knows how to improve upon --- for example, a
         * two-term `+1` / `-1` inequality is a difference constraint. They are
         * deliberately the constructor's arguments and nothing else: no
         * prepare()-time snapshot is exposed, because a presolver runs with a
         * State and can ask that for current bounds itself.
         *
         * Note that this is the *normalised* form. LinearGreaterThanEqual and
         * friends negate their coefficients and their right-hand side in their
         * constructors, so they read back as the `<=` they became; and because
         * clone() (which is what Problem stores) returns a
         * ReifiedLinearInequality whatever the derived type was, the reification
         * condition, not the C++ type, is what distinguishes the plain form from
         * the `If` and `Iff` ones.
         *
         * @{
         */

        /**
         * \brief The weighted terms on the left hand side, as posted, with
         * constants appearing as ConstantIntegerVariableID.
         */
        [[nodiscard]] auto coefficients_and_variables() const GCS_LIFETIME_BOUND -> const WeightedSum &
        {
            return _coeff_vars;
        }

        /**
         * \brief The right hand side, as posted.
         */
        [[nodiscard]] auto value() const -> Integer
        {
            return _value;
        }

        /**
         * \brief The reification condition, as posted: reif::MustHold for a
         * plain LinearLessThanEqual, reif::If for the `If` form, and so on.
         */
        [[nodiscard]] auto reification_condition() const GCS_LIFETIME_BOUND -> const ReificationCondition &
        {
            return _reif_cond;
        }

        ///@}
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief The rows ReifiedLinearInequality commits to keeping citable.
     *
     * \ingroup Innards
     */
    template <>
    struct innards::ConstraintProofModelData<ReifiedLinearInequality>
    {
        /**
         * \brief The role of the row stating `sum <= value`, under the
         * reification condition if there is one.
         *
         * Public API: the difference-logic presolver builds `pol`s on this row.
         * Changing which row this names is a breaking change.
         *
         * MustHold and If both use the empty role, so both come out as
         * `@c[<id>]`. The other three publish nothing. MustNotHold's empty-role
         * row states the integer negation and Iff's `r` / `f` halves state the
         * two directions of the equivalence, so neither is the row a citer
         * asking for `sum <= value` means. NotIf is excluded for a different and
         * less comfortable reason: its `ltn` row is emitted as
         * `cond -> sum <= value`, which is what the constraint says must *not*
         * hold, so the row as written looks wrong rather than merely unwanted.
         * Nothing in gcs constructs a ReifiedLinearInequality with either
         * negated kind --- the six derived classes cover MustHold, If and Iff,
         * and scp_reader builds only those --- so this publishes nothing rather
         * than committing to a row that has never been exercised.
         *
         * A nullopt here means "no such row exists", which is different from a
         * nullopt out of NamesAndIDsTracker::constraint_row_label, where the row
         * exists in principle but was not emitted (no proof was being logged,
         * say).
         */
        [[nodiscard]] static auto primary_row_role(const ReifiedLinearInequality &) -> std::optional<std::string>;
    };
}

#endif
