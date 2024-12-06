#ifndef GLASGOW_CONSTRAINT_SOLVER_CONSTRAINTS_ALL_DIFFERENT_ENCODING_HH
#define GLASGOW_CONSTRAINT_SOLVER_CONSTRAINTS_ALL_DIFFERENT_ENCODING_HH

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
        auto define_clique_not_equals_encoding(ProofModel & model,
            const std::vector<IntegerVariableID> & vars) -> void;
    }
}

#endif
