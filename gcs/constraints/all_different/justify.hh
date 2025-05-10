#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_JUSTIFY_HH

#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <vector>

namespace gcs::innards
{
    auto justify_all_different_hall_set_or_violator(
        ProofLogger &,
        const std::vector<IntegerVariableID> & all_variables,
        const std::vector<IntegerVariableID> & hall_variables,
        const std::vector<Integer> & hall_values,
        std::map<Integer, ProofLine> & constraint_numbers) -> void;
}

#endif
