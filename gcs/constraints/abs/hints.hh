#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief abs's assertion hint: just the owning constraint.
     *
     * abs needs no per-shape discriminator. One justification function reads the
     * asserted literal and the reason and dispatches on them, so there is nothing
     * for the wire to disambiguate -- every abs bound is re-derivable from the
     * asserted literal, the reason and the definition lines. The same hint rides
     * both JustifyUsingRUP (the pure-RUP pruning) and JustifyExplicitly (the
     * explicit-steps bounds): the assertion-hint axis is orthogonal to how the
     * inference is proved. With no own hint_sexpr it takes the default wire form,
     * `(constraint_id <originator>)`.
     *
     * \ingroup Innards
     */
    struct Abs
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "abs";
    };
}

#endif
