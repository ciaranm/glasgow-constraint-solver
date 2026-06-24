#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_2D_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_2D_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief Disjunctive2D's assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct Disjunctive2D
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "disjunctive_2d";
    };
}

#endif
