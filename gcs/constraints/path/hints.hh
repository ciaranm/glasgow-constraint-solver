#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PATH_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PATH_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief The path family's assertion hint: just the owning constraint, no
     * subhint.
     *
     * Both spellings use it, as Reachable and DReachable share theirs; see
     * gcs/constraints/tree/hints.hh.
     *
     * \ingroup Innards
     */
    struct Path
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "path";
    };
}

#endif
