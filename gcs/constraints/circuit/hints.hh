#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief Circuit's assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct Circuit
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "circuit";
    };
}

#endif
