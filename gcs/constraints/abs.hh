#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>

namespace gcs
{
    /**
     * \brief Absolute value constraint, `v2 = abs(v1)`.
     *
     * \ingroup Constraints
     */
    class Abs : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;

        // Captured in define_proof_model() for use by the consequence-bound
        // initialisers' PB-resolution proof steps. Each pair is (≤ half line,
        // ≥ half line) of the half-reified equality.
        std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>> _abs_nonneg_lines;
        std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>> _abs_neg_lines;

        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Abs(const IntegerVariableID v1, const IntegerVariableID v2);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;

        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
