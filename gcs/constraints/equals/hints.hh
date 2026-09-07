#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HINTS_HH

#include <gcs/constraint_id.hh>
#include <gcs/constraints/innards/equals_mutations.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/reason.hh>
#include <gcs/variable_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief equals's base assertion hint: just the owning constraint.
     *
     * Used directly for the pure-RUP prunings (a value forced out of one operand
     * because the other is fixed, the bound tightenings, the singleton reified
     * verdicts). RUP-derivable, so no emit_justification and no subhint; it takes
     * the default `(constraint_id <originator>)` wire form.
     *
     * The bare form therefore means "one RUP against the equality rows" and
     * nothing else. Every derivation in the family that needs lemmas emitted
     * ahead of its conclusion names a subhint: EqualsNotInRange below for the
     * interval bridge, EqualsNoOverlap for the disjointness walk.
     *
     * \ingroup Innards
     */
    struct Equals
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "equals";
    };

    /**
     * \brief equals's "not in this interval, across the equality" hint.
     *
     * The symmetric-difference rule's conclusion is a range literal, and a range
     * literal asserts only order atoms while the equality rows are a bit-sum, so
     * the conclusion is not RUP on its own: two ge-layer bound lemmas have to
     * carry its endpoints across first (justify_not_in_range_across_equality).
     * That makes it a three-line derivation wearing, until issue #866, the same
     * wire form as the family's one-line RUP prunings -- so the only way to tell
     * them apart was to notice that the asserted literal was spelled as a range,
     * which is keying off literal spelling, exactly what the hint vocabulary
     * exists to avoid.
     *
     * Nothing beyond the subhint: the emission is a lambda at the call site
     * rather than an emit_justification here, and an external justifier gets the
     * interval and the operands from the asserted literal and the reason.
     *
     * \ingroup Innards
     */
    struct EqualsNotInRange : Equals
    {
        static constexpr std::string_view subhint_name = "not_in_range";
    };

    /**
     * \brief equals's "domains don't overlap" hint, carried in a reified verdict.
     *
     * Extends the base with the `no_overlap` subhint and the only context the
     * lemmas cannot be written without: the two operands and the reification
     * condition, which is what the lemmas are *about*. The walk itself comes out
     * of the reason at emit time, so nothing here describes the domains, and no
     * State pointer is held -- a justification may read the reason and the
     * model, and anything it reads out of state is a bound that has since moved
     * (issue #870). The data is held for emit_justification only; with no own
     * hint_sexpr the hint takes the default identity-plus-subhint wire form.
     *
     * The reason's spelling of a run does not change the lemmas, though it does
     * decide where they fall: a run is stepped over inside one variable, by its
     * range literal's reverse reification or by its eq atoms walking the order
     * chain, and either way the witness owes that step nothing.
     *
     * The mutation is testing-only and is carried here because this is the only
     * place it can be: the emission is an emit_justification rather than a
     * lambda at the call site, so the hint is the whole of what it is handed.
     * See EqualsProofMutation.
     *
     * \ingroup Innards
     */
    struct EqualsNoOverlap : Equals
    {
        static constexpr std::string_view subhint_name = "no_overlap";
        IntegerVariableID v1, v2;
        Literal cond;
        EqualsProofMutation mutation = equals_proof_mutation::None{};
    };

    auto emit_justification(ProofLogger & logger, const EqualsNoOverlap & no_overlap, const ReasonLiterals & reason) -> void;
}

#endif
