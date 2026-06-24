#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SORT_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SORT_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief Sort's assertion hint: just the owning constraint.
     *
     * Sort and ArgSort share the Mehlhorn-Thiel sortedness propagator; its
     * inferences carry this hint with the real owning constraint id (Sort's own
     * id, or ArgSort's, depending on who installed the propagator). Every bound
     * and contradiction is re-derivable from the asserted literal, the reason and
     * the witness definition lines, so there is no per-shape discriminator and the
     * hint takes the default `(constraint_id <originator>)` wire form.
     *
     * \ingroup Innards
     */
    struct Sort
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "sort";
    };

    /**
     * \brief ArgSort's assertion hint: just the owning constraint.
     *
     * Carried by ArgSort's own channel-consistency and achievable-rank-set
     * propagators (the inner sortedness propagator uses the Sort hint above, and
     * the permutation all_different reuse carries the all_different hints). No
     * per-shape discriminator; default `(constraint_id <originator>)` wire form.
     *
     * \ingroup Innards
     */
    struct ArgSort
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "arg_sort";
    };
}

#endif
