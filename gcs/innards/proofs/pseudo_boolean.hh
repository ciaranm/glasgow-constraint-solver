#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PSEUDO_BOOLEAN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PSEUDO_BOOLEAN_HH

#include <gcs/expression.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>

#include <util/overloaded.hh>

namespace gcs::innards
{
    /**
     * \brief Inside a Proof, a pseudo-Boolean expression can contain a ProofLiteral,
     * a ProofFlag, an IntegerVariableID or ProofOnlySimpleIntegerVariableID
     * to be decomposed into its bits.
     *
     * \ingroup Innards
     */
    using PseudoBooleanTerm = std::variant<ProofLiteral, ProofFlag, IntegerVariableID, ProofOnlySimpleIntegerVariableID, ProofBitVariable>;

    using WPBSum = SumOf<Weighted<PseudoBooleanTerm>>;

    using WPBSumLE = SumLessThanEqual<Weighted<PseudoBooleanTerm>>;

    using WPBSumEq = SumEquals<Weighted<PseudoBooleanTerm>>;

    /**
     * \brief Add `coefficient * term` to a sum, over the three things a
     * ProofLiteralOrFlag can be.
     *
     * Every alternative of ProofLiteralOrFlag is also one of
     * PseudoBooleanTerm, so this only widens --- but widening a variant is a
     * visit rather than a conversion, and it is worth writing once rather than
     * once per caller that takes its terms in the narrower type.
     *
     * \ingroup Innards
     */
    inline auto add_term_to(WPBSum & sum, Integer coefficient, const ProofLiteralOrFlag & term) -> void
    {
        overloaded{                                                      //
            [&](const ProofLiteral & l) { sum += coefficient * l; },     //
            [&](const ProofFlag & f) { sum += coefficient * f; },        //
            [&](const ProofBitVariable & b) { sum += coefficient * b; }} //
            .visit(term);
    }
}

#endif
