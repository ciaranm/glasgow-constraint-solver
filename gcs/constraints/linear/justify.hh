#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_JUSTIFY_HH

#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <utility>
#include <vector>

namespace gcs::innards
{
    auto justify_linear_bounds(
        ProofLogger & logger,
        const auto & coeff_vars,
        const std::vector<std::pair<Integer, Integer>> & bounds,
        const SimpleIntegerVariableID & which_var_is_changing,
        bool use_second_constraint_for_equality,
        ProofLine proof_line) -> void;
}

#endif
