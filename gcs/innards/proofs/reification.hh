#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_REIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_REIFICATION_HH

#include <gcs/innards/proofs/pseudo_boolean.hh>

#include <vector>

namespace gcs::innards
{
    /**
     * \brief Various things in Proof can reify on a conjunction of
     * ProofLiteral and ProofFlag.
     *
     * \ingroup Innards
     */
    using HalfReifyOnConjunctionOf = std::vector<ProofLiteralOrFlag>;

}

#endif
