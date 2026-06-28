#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH 1

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/expression.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators-fwd.hh>
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

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        // Takes State (unlike the base's Propagators-only hook) because the incremental
        // must-hold path registers backtrackable constraint state at install time.
        auto install_propagators(innards::Propagators &, innards::State &) -> void;

    public:
        explicit ReifiedLinearInequality(
            WeightedSum coeff_vars, Integer value, ReificationCondition cond, std::optional<std::size_t> incremental_threshold = std::nullopt);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
    };
}

#endif
