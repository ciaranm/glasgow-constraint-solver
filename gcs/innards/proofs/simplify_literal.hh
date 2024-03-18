#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_SIMPLIFY_LITERAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_SIMPLIFY_LITERAL_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/variable_condition.hh>

#include <variant>

namespace gcs::innards
{
    using SimpleLiteral = std::variant<VariableConditionFrom<SimpleIntegerVariableID>,
        ProofVariableCondition, TrueLiteral, FalseLiteral>;

    /**
     * Simplify a ProofLiteral down by removing some of the more awkward possible
     * variants.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto simplify_literal(const ProofLiteral & lit) -> SimpleLiteral;
}

#endif
