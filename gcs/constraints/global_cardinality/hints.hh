#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief GlobalCardinality's assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct GlobalCardinality
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "global_cardinality";
    };
}

#endif
