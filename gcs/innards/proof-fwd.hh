/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_FWD_HH

namespace gcs::innards
{
    class Proof;

    struct ProofFlag;

    /**
     * A proof line number, corresponding to a VeriPB constraint number.
     *
     * \ingroup Innards
     */
    using ProofLine = long long;

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
