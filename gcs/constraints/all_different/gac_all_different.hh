#ifndef GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    namespace innards
    {
        auto propagate_gac_all_different(const ConstraintID & constraint_id, const std::vector<IntegerVariableID> & vars,
            const std::vector<Integer> & vals, const std::vector<Integer> & excluded, std::map<Integer, ProofLine> & value_am1_constraint_numbers,
            const State & state, auto & inference_tracker, ProofLogger * const logger) -> void;
    }

}
#endif // GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH
