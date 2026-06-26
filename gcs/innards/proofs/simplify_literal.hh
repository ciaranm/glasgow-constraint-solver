#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_SIMPLIFY_LITERAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_SIMPLIFY_LITERAL_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/variable_condition.hh>

#include <variant>

namespace gcs::innards
{
    using SimpleLiteral = std::variant<VariableConditionFrom<SimpleIntegerVariableID>, ProofVariableCondition, TrueLiteral, FalseLiteral>;

    /**
     * Simplify a ProofLiteral down by removing some of the more awkward possible
     * variants.
     *
     * For literals on a `ViewOfIntegerVariableID`, the result depends on
     * whether the view has been registered with the tracker (typical case:
     * yes, having been seen during model writing). If so, returns a
     * `ProofVariableCondition` over `BinEnc(view)` (V's own bits), preserving
     * the literal's op and value verbatim. If not registered (only happens
     * for views first seen during proof logging), deviews through the
     * underlying as before.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto simplify_literal(const NamesAndIDsTracker & tracker, const ProofLiteral & lit) -> SimpleLiteral;
}

#endif
