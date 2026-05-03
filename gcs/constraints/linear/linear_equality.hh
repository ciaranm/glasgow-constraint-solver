#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_EQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_EQUALITY_HH

#include <gcs/constraint.hh>
#include <gcs/expression.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/reification.hh>

#include <optional>
#include <utility>

namespace gcs
{
    /**
     * \brief Constrain that the sum of the variables multiplied by their associated
     * coefficients is equal to the specified value, potentially subject to a reification
     * condition.
     *
     * If gac is specifed, achieves generalised arc consistency. This is very
     * expensive for large variables.
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
        bool _gac;
        bool _flipped_cond;
        std::optional<std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>>> _proof_line;
        innards::EvaluatedReificationCondition _evaluated_cond = innards::evaluated_reif::Deactivated{};

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit ReifiedLinearEquality(WeightedSum coeff_vars, Integer value, ReificationCondition reif_cond, bool gac = false, bool flipped_cond = false);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };

    class LinearEquality : public ReifiedLinearEquality
    {
    public:
        explicit LinearEquality(WeightedSum coeff_vars, Integer value, bool gac = false);
    };

    class LinearEqualityIf : public ReifiedLinearEquality
    {
    public:
        explicit LinearEqualityIf(WeightedSum coeff_vars, Integer value, innards::Literal cond, bool gac = false);
    };

    class LinearEqualityIff : public ReifiedLinearEquality
    {
    public:
        explicit LinearEqualityIff(WeightedSum coeff_vars, Integer value, innards::Literal cond, bool gac = false);
    };

    class LinearNotEquals : public ReifiedLinearEquality
    {
    public:
        explicit LinearNotEquals(WeightedSum coeff_vars, Integer value, bool gac = false);
    };

    class LinearNotEqualsIf : public ReifiedLinearEquality
    {
    public:
        explicit LinearNotEqualsIf(WeightedSum coeff_vars, Integer value, innards::Literal cond, bool gac = false);
    };

    class LinearNotEqualsIff : public ReifiedLinearEquality
    {
    public:
        explicit LinearNotEqualsIff(WeightedSum coeff_vars, Integer value, innards::Literal cond, bool gac = false);
    };
}

#endif
