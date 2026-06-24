#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TABLE_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TABLE_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief Table's assertion hint: just the owning constraint.
     *
     * Table's propagation runs through the shared helper propagate_extensional()
     * (gcs/constraints/extensional_utils.hh), which takes a typed hint; Table passes
     * this so the helper's RUP prunings and contradictions name it. Each is
     * re-derivable from the asserted literal, the reason and the tuple definition
     * lines, so the hint carries no per-shape discriminator and takes the default
     * `(constraint_id <originator>)` wire form.
     *
     * \ingroup Innards
     */
    struct Table
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "table";
    };

    /**
     * \brief NegativeTable's assertion hint: just the owning constraint.
     *
     * The watched-literal propagator's prunings and contradictions are each
     * re-derivable from the asserted literal, the reason and the forbidden-tuple
     * definition lines, so the hint carries no per-shape discriminator and takes
     * the default `(constraint_id <originator>)` wire form.
     *
     * \ingroup Innards
     */
    struct NegativeTable
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "negative_table";
    };
}

#endif
