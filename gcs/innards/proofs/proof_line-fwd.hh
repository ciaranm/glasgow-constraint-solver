#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LINE_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LINE_FWD_HH

#include <variant>

namespace gcs::innards
{
    struct ProofLineNumber;
    struct ProofLineLabel;

    /**
     * A proof line, corresponding to either a VeriPB constraint number or a
     * constraint label.
     *
     * \ingroup Innards
     */
    using ProofLine = std::variant<ProofLineNumber, ProofLineLabel>;
}

#endif
