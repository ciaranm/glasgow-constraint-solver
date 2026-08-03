#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief Cumulative's assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct Cumulative
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "cumulative";
    };

    /**
     * \brief Cumulative's overload-check hint: the owning constraint, plus the
     * `overload` subhint distinguishing an energy-based conflict from a
     * time-table one.
     *
     * The two rules reach a contradiction by quite different derivations, so
     * telling them apart matters when isolating one with
     * AssertRatherThanJustifying. With no own hint_sexpr the hint takes the
     * default identity-plus-subhint wire form,
     * `(constraint_id <originator>)(subhint overload)`.
     *
     * \ingroup Innards
     */
    struct CumulativeOverload : Cumulative
    {
        static constexpr std::string_view subhint_name = "overload";
    };
}

#endif
