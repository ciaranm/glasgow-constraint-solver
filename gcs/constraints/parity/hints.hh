#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief ParityOdd's assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct Parity
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "parity";
    };
}

#endif
