#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_AT_MOST_ONE_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_AT_MOST_ONE_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief AtMostOne's assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct AtMostOne
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "at_most_one";
    };
}

#endif
