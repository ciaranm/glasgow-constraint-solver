#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_EQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_EQUALITY_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/expression.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/reification.hh>

#include <cstddef>
#include <optional>
#include <utility>
#include <variant>

namespace gcs
{
    /**
     * \brief The consistency levels supported by the linear equality family:
     * bounds consistency (the default), or generalised arc consistency.
     *
     * \ingroup Consistency
     */
    using LinearEqualityConsistency = std::variant<consistency::BC, consistency::Tabulated>;

    /**
     * \brief Constrain that the sum of the variables multiplied by their associated
     * coefficients is equal to the specified value, potentially subject to a reification
     * condition.
     *
     * If consistency::Tabulated is requested, achieves generalised arc consistency.
     * This is very expensive for large variables.
     *
     * \ingroup Constraints
     * \sa LinearLessThanEqual
     * \sa LinearGreaterThanEqual
     * \sa LinearEquality
     */
    class ReifiedLinearEquality : public Constraint
    {
    private:
        WeightedSum _coeff_vars;
        Integer _value;
        ReificationCondition _reif_cond;
        bool _flipped_cond;
        LinearEqualityConsistency _level = consistency::BC{};
        // Per-constraint width at/above which to use the incremental propagator; unset
        // means use innards::default_linear_incremental_threshold().
        std::optional<std::size_t> _incremental_threshold = std::nullopt;
        std::optional<std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>>> _proof_line;
        innards::EvaluatedReificationCondition _evaluated_cond = innards::evaluated_reif::Deactivated{};

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        // Takes State (unlike the base's Propagators-only hook) because the incremental
        // equality path registers backtrackable constraint state at install time.
        auto install_propagators(innards::Propagators &, innards::State &) -> void;

    public:
        // flipped_cond is internal reification plumbing, set by the derived NotEqualsIff
        // form; it is not user configuration. Propagation strength and the incremental
        // threshold are chosen after construction via with_consistency() and
        // with_incremental_threshold().
        explicit ReifiedLinearEquality(WeightedSum coeff_vars, Integer value, ReificationCondition reif_cond, bool flipped_cond = false);

        /**
         * \brief Select the consistency level: bounds consistency (the default) or
         * consistency::Tabulated. Requesting any other level is a compile-time error.
         */
        auto with_consistency(LinearEqualityConsistency level) -> ReifiedLinearEquality &;

        /**
         * \brief Set the per-constraint scope width at or above which the incremental
         * (fixed-term-folding) propagator is used; unset means the solver default.
         */
        auto with_incremental_threshold(std::optional<std::size_t> threshold) -> ReifiedLinearEquality &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
    };

    class LinearEquality : public ReifiedLinearEquality
    {
    public:
        explicit LinearEquality(WeightedSum coeff_vars, Integer value);
    };

    class LinearEqualityIf : public ReifiedLinearEquality
    {
    public:
        explicit LinearEqualityIf(WeightedSum coeff_vars, Integer value, innards::Literal cond);
    };

    class LinearEqualityIff : public ReifiedLinearEquality
    {
    public:
        explicit LinearEqualityIff(WeightedSum coeff_vars, Integer value, innards::Literal cond);
    };

    class LinearNotEquals : public ReifiedLinearEquality
    {
    public:
        explicit LinearNotEquals(WeightedSum coeff_vars, Integer value);
    };

    class LinearNotEqualsIf : public ReifiedLinearEquality
    {
    public:
        explicit LinearNotEqualsIf(WeightedSum coeff_vars, Integer value, innards::Literal cond);
    };

    class LinearNotEqualsIff : public ReifiedLinearEquality
    {
    public:
        explicit LinearNotEqualsIff(WeightedSum coeff_vars, Integer value, innards::Literal cond);
    };
}

#endif
