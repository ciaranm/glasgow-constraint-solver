/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SEARCH_HEURISTICS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SEARCH_HEURISTICS_HH

#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <functional>

namespace gcs
{
    /**
     * \defgroup SearchHeuristics Common search heuristics for gcs::solve_with
     *
     * \sa SolveCallbacks
     */

    /**
     * Used by gcs::branch_on_smallest_with_respect_to as a less-than comparator.
     *
     * \ingroup SearchHeuristics
     * \sa gcs::branch_on_smallest_with_respect_to()
     */
    using BranchVariableComparator = std::function<auto(const CurrentState &, IntegerVariableID, IntegerVariableID)->bool>;

    /**
     * Branch on whichever variable is smallest with respect to the provided
     * less-than comparator.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_on_smallest_with_respect_to(
        const Problem & problem,
        const std::vector<IntegerVariableID> &,
        const BranchVariableComparator &) -> BranchCallback;

    /**
     * Branch on smallest domain from the supplied variables.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_on_dom(const Problem & problem, const std::vector<IntegerVariableID> &) -> BranchCallback;

    /**
     * Branch on smallest domain from all variables.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_on_dom(const Problem & problem) -> BranchCallback;

    /**
     * Branch on smallest domain, tie-breaking on degree, from the supplied
     * variables.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_on_dom_then_deg(const Problem & problem, const std::vector<IntegerVariableID> &) -> BranchCallback;

    /**
     * Branch on smallest domain, tie-breaking on degree, from all variables.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_on_dom_then_deg(const Problem & problem) -> BranchCallback;

    /**
     * Guess values from smallest to largest.
     *
     * \ingroup SearchHeuristics
     */
    auto guess_smallest_value_first() -> GuessCallback;
}

#endif
