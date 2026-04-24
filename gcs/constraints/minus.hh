#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MINUS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MINUS_HH

#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>

namespace gcs
{
    /**
     * \brief Constrain that a - b = result.
     *
     * \ingroup Constraints
     */
    class Minus : public Constraint
    {
    private:
        IntegerVariableID _a, _b, _result;
        std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>> _sum_line;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Minus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
