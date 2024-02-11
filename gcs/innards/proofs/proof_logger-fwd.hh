#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LOGGER_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LOGGER_FWD_HH

namespace gcs::innards
{
    class ProofLogger;

    /**
     * Controls deletions of constraints inside a proof. Items written at level
     * Current are erased on backtrack, and items in Temporary are erased at
     * the end of the current propagation section.
     *
     * \ingroup Innards
     */
    enum class ProofLevel
    {
        Current,
        Top,
        Temporary
    };

    /**
     * A proof line number, corresponding to a VeriPB constraint number.
     *
     * \ingroup Innards
     */
    using ProofLine = long long;
}

#endif
