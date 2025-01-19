#ifndef GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH

#include <gcs/constraint.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/proofs/lp_justification.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <vector>

namespace gcs
{
    namespace innards
    {
        auto propagate_gac_all_different(
            const std::vector<IntegerVariableID> & vars,
            const std::vector<Integer> & vals,
            const std::map<Integer, ProofLine> * const am1_value_constraint_numbers,
            const State & state,
            auto & inference_tracker,
            ProofLogger * const logger,
            const std::map<ProofLine, WeightedPseudoBooleanLessEqual> * const pb_constraints = nullptr,
            const std::optional<LPJustificationOptions> lp_justification_options = std::nullopt) -> void;
    }

    /**
     * \brief GAC all different constraint, each var takes a different value, and do GAC pruning.
     *
     * \ingroup Constraints
     * \sa NValue
     */
    class GACAllDifferent : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        const std::optional<LPJustificationOptions> _lp_justification_options;

    public:
        explicit GACAllDifferent(std::vector<IntegerVariableID> vars, std::optional<LPJustificationOptions> lp_justification_options = std::nullopt);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

}
#endif // GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH
