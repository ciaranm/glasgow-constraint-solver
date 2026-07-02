#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIVIDE_MODULUS_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIVIDE_MODULUS_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief Divide's assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct Divide
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "divide";
    };

    /**
     * \brief Modulus's assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct Modulus
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "modulus";
    };
}

#endif
