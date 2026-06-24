#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LOGICAL_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LOGICAL_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief And's assertion hint: just the owning constraint.
     *
     * And and Or share one reified-conjunction propagator (Or is And over the
     * negated literals and reif), but each posts its own constraint id, so the
     * hint family name distinguishes the two on the wire. Every inference is
     * re-derivable from the asserted literal, the reason and the definition
     * lines, so there is no per-shape discriminator and the hint takes the
     * default `(constraint_id <originator>)` wire form.
     *
     * \ingroup Innards
     */
    struct And
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "and";
    };

    /**
     * \brief Or's assertion hint: just the owning constraint.
     *
     * The mirror of And (see above): same shared propagator, distinct family
     * name, no per-shape discriminator.
     *
     * \ingroup Innards
     */
    struct Or
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "or";
    };
}

#endif
