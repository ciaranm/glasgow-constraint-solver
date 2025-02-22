#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <gcs/innards/proofs/proof_logger.hh>

#include <optional>
#include <utility>

namespace gcs
{
    /**
     * \brief Constrain that a + b = result.
     *
     * \ingroup Constraints
     */
    class Plus : public Constraint
    {
    private:
        IntegerVariableID _a, _b, _result;

    public:
        explicit Plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

    namespace innards
    {
        [[nodiscard]] auto propagate_plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result,
            const State &,
            auto & inference,
            ProofLogger * const,
            const std::pair<std::optional<ProofLine>, std::optional<ProofLine>> &) -> PropagatorState;
    }
}

#endif
