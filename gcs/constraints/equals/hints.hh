#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HINTS_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <string_view>
#include <utility>

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
     * \ingroup Innards
     */
    struct Equals
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "equals";
    };

    /**
     * \brief equals's "domains don't overlap" hint, carried in a reified verdict.
     *
     * Extends the base with the `no_overlap` subhint and the emit context the
     * internal proof writer reads to re-walk the disjointness: the operands and
     * the reification condition. The State pointer is valid because the verdict
     * is consumed synchronously while the constraint is live. The data is held
     * for emit_justification only; with no own hint_sexpr the hint takes the
     * default identity-plus-subhint wire form.
     *
     * Nothing here says how the reason spelled its runs, because the lemmas do
     * not depend on it: a run is stepped over inside one variable, by its range
     * literal's reverse reification or by its eq atoms walking the order chain,
     * and either way the witness owes it nothing.
     *
     * \ingroup Innards
     */
    struct EqualsNoOverlap : Equals
    {
        static constexpr std::string_view subhint_name = "no_overlap";
        const State * state;
        IntegerVariableID v1, v2;
        Literal cond;
    };

    auto emit_justification(ProofLogger & logger, const EqualsNoOverlap & no_overlap, const ReasonLiterals & reason) -> void;
}

#endif
