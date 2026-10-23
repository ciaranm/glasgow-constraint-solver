#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief Knapsack's assertion hint: just the owning constraint.
     *
     * Used by the default per-call Knapsack propagator.
     *
     * \ingroup Innards
     */
    struct Knapsack
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "knapsack";
    };

    /**
     * \brief The assertion hint of Knapsack's proof_strategy::Upfront: just
     * the owning constraint.
     *
     * Used by the opt-in upfront-DAG strategy (knapsack_upfront.cc).
     *
     * \ingroup Innards
     */
    struct KnapsackUpfront
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "knapsack_upfront";
    };
}

#endif
