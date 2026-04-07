#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_ONLY_VARIABLES_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_ONLY_VARIABLES_FWD_HH

#include <gcs/variable_id-fwd.hh>

#include <variant>

namespace gcs::innards
{
    struct ProofOnlySimpleIntegerVariableID;

    using SimpleOrProofOnlyIntegerVariableID = std::variant<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID>;

    struct ProofFlag;
}

#endif
