#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INVERSE_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INVERSE_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief Inverse's assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct Inverse
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "inverse";
    };

    /**
     * \brief Inverse's injection form: a value of the second array's index set
     * that every matching of the first array takes, so the entry of the second
     * array at that index can only name an entry of the first that can take it.
     * Justified by a Hall set summed without that value's at-most-one.
     *
     * \ingroup Innards
     */
    struct InverseNeededValue : Inverse
    {
        static constexpr std::string_view subhint_name = "needed_value";
    };
}

#endif
