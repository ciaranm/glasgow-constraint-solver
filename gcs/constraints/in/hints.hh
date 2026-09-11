#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_IN_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_IN_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief In's base assertion hint: just the owning constraint.
     *
     * Carried by the per-value prunings, both directions: a value dropped from
     * `var` because no source holds it, and a value dropped from the single
     * supporting source because `var` does not hold it. Either way the
     * derivation is one scaffolding line per selector and then RUP, and which
     * of the two it is follows from which variable the asserted literal is
     * about -- `var` or a source.
     *
     * \ingroup Innards
     */
    struct In
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "in";
    };

    /**
     * \brief In's "not in this interval" hint, for either range pruning.
     *
     * A range literal asserts only order atoms while the selectors' rows are a
     * bit-sum, so a range conclusion is not RUP on its own: the two ge-layer
     * bound lemmas of justify_not_in_range_across_equality have to carry its
     * endpoints across the selector's equality first. That makes it a
     * several-line derivation wearing, without this, the same wire form as the
     * one-line-per-selector prunings above -- and telling them apart by noticing
     * that the asserted literal is spelled as a range is keying off literal
     * spelling, which is what the hint vocabulary exists to avoid (issue #866).
     *
     * One subhint for both range prunings, for the same reason the base hint
     * covers both per-value ones: the asserted literal's variable says which,
     * and the two derivations are the same lemmas either side of the equality.
     * Nothing beyond the subhint -- the emission is a lambda at the call site,
     * and an external justifier gets the interval, the operands and the
     * selectors from the asserted literal and the reason.
     *
     * \ingroup Innards
     */
    struct InNotInRange : In
    {
        static constexpr std::string_view subhint_name = "not_in_range";
    };
}

#endif
