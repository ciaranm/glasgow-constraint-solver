#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_REIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_REIFICATION_HH

#include <gcs/innards/proofs/pseudo_boolean.hh>

#include <gch/small_vector.hpp>

#include <vector>

namespace gcs::innards
{
    /**
     * \brief Various things in Proof can reify on a conjunction of
     * ProofLiteral and ProofFlag.
     *
     * Conjunctions are usually short (1–3 elements). Inline capacity 2
     * keeps the common cases off the heap; longer conjunctions still
     * work via fallback heap allocation.
     *
     * \ingroup Innards
     */
    using HalfReifyOnConjunctionOf = gch::small_vector<ProofLiteralOrFlag, 2>;
}

#endif
