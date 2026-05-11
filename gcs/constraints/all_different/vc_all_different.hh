#ifndef GLASGOW_CONSTRAINT_SOLVER_VC_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_VC_ALL_DIFFERENT_HH

#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>
#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    namespace innards
    {
        auto propagate_non_gac_alldifferent(
            const ConstraintStateHandle & unassigned_handle, const State & state,
            auto & inference_tracker, ProofLogger * const logger) -> void;
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
        std::vector<IntegerVariableID> _sanitised_vars;
        innards::ConstraintStateHandle _unassigned_handle;
        bool _has_duplicate_vars = false;
        std::optional<std::pair<IntegerVariableID, innards::ProofFlag>> _duplicate_witness;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit VCAllDifferent(std::vector<IntegerVariableID> vars);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}
#endif // GLASGOW_CONSTRAINT_SOLVER_VC_ALL_DIFFERENT_HH
