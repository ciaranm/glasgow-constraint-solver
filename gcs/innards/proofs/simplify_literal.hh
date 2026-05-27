#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_SIMPLIFY_LITERAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_SIMPLIFY_LITERAL_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/variable_condition.hh>

#include <variant>

namespace gcs::innards
{
    using SimpleLiteral = std::variant<VariableConditionFrom<SimpleIntegerVariableID>,
        ProofVariableCondition, TrueLiteral, FalseLiteral>;

    /**
     * \brief Simplify a ProofLiteral down to a form that names the variable
     * by its proof identity.
     *
     * For SimpleIntegerVariableID and ConstantIntegerVariableID, this is a
     * direct translation. For ViewOfIntegerVariableID, the literal is routed
     * through the view's *extension* variable (`NamesAndIDsTracker::extension_for`):
     * `v >= k` becomes `extension(v) >= k` without any value adjustment,
     * because the extension's value equals the view's value. This keeps the
     * resulting proof literal bit-clean against the constraint's
     * extension-form encoding. Bridges that tie the extension's atomic
     * literals to the underlying variable's atomic literals are emitted
     * lazily at gevar-introduction time (see `NamesAndIDsTracker::need_gevar`).
     *
     * Calling this function on a view will allocate the extension if it
     * doesn't already exist, which requires a `ProofModel` to be active.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto simplify_literal(NamesAndIDsTracker & tracker, const ProofLiteral & lit) -> SimpleLiteral;
}

#endif
