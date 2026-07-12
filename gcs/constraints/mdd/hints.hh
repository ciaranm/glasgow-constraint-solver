#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MDD_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MDD_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief MDD's assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct MDD
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "mdd";
    };
}

#endif
