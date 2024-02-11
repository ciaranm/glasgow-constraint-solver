#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PSEUDO_BOOLEAN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PSEUDO_BOOLEAN_HH

#include <gcs/expression.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>

namespace gcs::innards
{
    /**
     * \brief Inside a Proof, a pseudo-Boolean expression can contain a ProofLiteral,
     * a ProofFlag, an IntegerVariableID or ProofOnlySimpleIntegerVariableID
     * to be decomposed into its bits.
     *
     * \ingroup Innards
     */
    using PseudoBooleanTerm = std::variant<ProofLiteral, ProofFlag, IntegerVariableID, ProofOnlySimpleIntegerVariableID>;

    using WeightedPseudoBooleanSum = SumOf<Weighted<PseudoBooleanTerm>>;

    using WeightedPseudoBooleanLessEqual = SumLessEqual<Weighted<PseudoBooleanTerm>>;

    using WeightedPseudoBooleanEquality = SumEquals<Weighted<PseudoBooleanTerm>>;
}

#endif
