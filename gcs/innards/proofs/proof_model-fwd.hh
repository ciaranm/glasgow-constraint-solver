#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_MODEL_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_MODEL_FWD_HH

namespace gcs::innards
{
    class ProofModel;

    /**
     * How should an IntegerVariableID be encoded in a proof?
     */
    enum class IntegerVariableProofRepresentation
    {
        DirectOnly, /// Just using the direct 0/1 encoding
        Bits        /// Use the bits encoding
    };
}

#endif
