#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_EMIT_INEQUALITY_TO_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_EMIT_INEQUALITY_TO_HH

#include <gcs/expression.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/proofs/variable_constraints_tracker-fwd.hh>

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
    auto emit_inequality_to(VariableConstraintsTracker &,
        const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
        const std::optional<HalfReifyOnConjunctionOf> & half_reif, std::ostream & stream) -> void;
}

#endif
