#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LINE_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LINE_FWD_HH

#include <boost/variant2/variant.hpp>

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
    using ProofLine = boost::variant2::variant<ProofLineNumber, ProofLineLabel>;
}

#endif
