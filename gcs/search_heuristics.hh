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
    using BranchVariableComparator = std::function<auto(const CurrentState &,
            const innards::Propagators &, IntegerVariableID, IntegerVariableID)->bool>;

    /**
     * Branch on whichever variable is smallest with respect to the provided
     * less-than comparator.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_on_smallest_with_respect_to(
        const std::vector<IntegerVariableID> &,
        const BranchVariableComparator &) -> BranchCallback;

    /**
     * Branch in order from the supplied variables.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_in_order(const std::vector<IntegerVariableID> &) -> BranchCallback;

    /**
     * Branch on smallest domain from the supplied variables.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_on_dom(const std::vector<IntegerVariableID> &) -> BranchCallback;

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
    auto branch_on_dom_then_deg(const std::vector<IntegerVariableID> &) -> BranchCallback;

    /**
     * Branch on smallest domain, tie-breaking on degree, from all variables.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_on_dom_then_deg(const Problem & problem) -> BranchCallback;

    /**
     * Branch on domain with smallest value in its domain, from the supplied variables.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_on_dom_with_smallest_value(const std::vector<IntegerVariableID> &) -> BranchCallback;

    /**
     * Branch on domain with smallest value in its domain, from all variables.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_on_dom_with_smallest_value(const Problem & problem) -> BranchCallback;

    /**
     * Try each branching heuristic in turn.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_sequence(const std::vector<BranchCallback> &) -> BranchCallback;

    /**
     * Branch on a randomly selected variable. This is usually not a good idea.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_randomly(const std::vector<IntegerVariableID> &) -> BranchCallback;

    /**
     * Branch on a randomly selected variable. This is usually not a good idea.
     *
     * \ingroup SearchHeuristics
     */
    auto branch_randomly(const Problem & problem) -> BranchCallback;

    /**
     * Guess values from smallest to largest.
     *
     * \ingroup SearchHeuristics
     */
    auto guess_smallest_value_first() -> GuessCallback;

    /**
     * Guess values from smallest to largest.
     *
     * \ingroup SearchHeuristics
     */
    auto guess_largest_value_first() -> GuessCallback;

    /**
     * Guess the median.
     *
     * \ingroup SearchHeuristics
     */
    auto guess_median_value() -> GuessCallback;

    /**
     * Guess values randomly.
     *
     * \ingroup SearchHeuristics
     */
    auto guess_randomly() -> GuessCallback;
}

#endif
