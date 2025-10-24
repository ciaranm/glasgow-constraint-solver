#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_JUSTIFY_HH

#include <gcs/innards/proofs/proof_logger.hh>

namespace gcs::innards
{
    auto justify_abs_hole(
        ProofLogger & logger,
        const ReasonFunction & reason,
        IntegerVariableID v1,
        IntegerVariableID v2,
        Integer val) -> void;
}

#endif
