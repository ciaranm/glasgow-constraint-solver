#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REACHABLE_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REACHABLE_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief The reachability family's assertion hint: just the owning constraint,
     * no subhint.
     *
     * \ingroup Innards
     */
    struct Reachable
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "reachable";
    };
}

#endif
