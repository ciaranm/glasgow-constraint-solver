#ifndef GLASGOW_CONSTRAINT_SOLVER_VC_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_VC_ALL_DIFFERENT_HH

#include <gcs/constraint.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>
#include <vector>

namespace gcs
{
    namespace innards
    {
        auto propagate_non_gac_alldifferent(
            const ConstraintStateHandle & unassigned_handle, const State & state,
            auto & inference_tracker, ProofLogger * const logger) -> void;

        auto define_clique_not_equals_encoding(ProofModel & model,
            const std::vector<IntegerVariableID> & vars) -> void;
    }

    /**
     * \brief "Value-consistent" all different constraint, each var takes a different value, but
     * only do minimum pruning to enforce this (only remove the value of fixed variables from the domains of the others).
     *
     * \ingroup Constraints
     * \sa NValue
     */
    class VCAllDifferent : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;

    public:
        explicit VCAllDifferent(std::vector<IntegerVariableID> vars);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}
#endif // GLASGOW_CONSTRAINT_SOLVER_VC_ALL_DIFFERENT_HH
