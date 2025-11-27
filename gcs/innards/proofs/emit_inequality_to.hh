#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_EMIT_INEQUALITY_TO_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_EMIT_INEQUALITY_TO_HH

#include <gcs/expression.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/reification.hh>

#include <iosfwd>

namespace gcs::innards
{
    /**
     * \brief Write an inequality out to an ostream.
     *
     * Only used inside proof innards.
     *
     * \ingroup Innards
     */
    auto emit_inequality_to(NamesAndIDsTracker &,
        const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
        std::ostream & stream) -> void;
}

#endif
