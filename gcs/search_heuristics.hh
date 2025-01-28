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
     * Specifies how to decide which variable to branch on, for SolveCallbacks. Usually this will be used
     * via the gcs::branch_with() function, which takes a BranchVariableSelector from the gcs::variable_order::
     * namespace and a BranchValueGenerator from the gcs::value_order:: namespace, but more elaborate options
     * that decide both a variable and a value together can be programmed. Can also be combined with other
     * heuristics in turn using gcs::branch_sequence(), e.g. to specify different value-orderings for different
     * variables. Returning nullopt means all relevant variables are already assigned.
     *
     * \ingroup SearchHeuristics
     */
    using BranchVariableSelector = std::function<std::optional<IntegerVariableID>(
        const CurrentState &, const innards::Propagators &)>;

    /**
     * Given a branch variable, how do we branch on it? Usually this will be used via the gcs::branch_with()
     * function, which takes a BranchVariableSelector from the gcs::variable_order:: namespace and a
     * BranchValueGenerator from the gcs::value_order:: namespace, but more elaborate options that decide
     * both a variable and a value together can be programmed. Can also be combined with other heuristics
     * in turn using gcs::branch_sequence(), e.g. to specify different value-orderings for different
     * variables.
     *
     * \ingroup SearchHeuristics
     */
    using BranchValueGenerator = std::function<std::generator<IntegerVariableCondition>(
        const CurrentState &, const innards::Propagators &, const IntegerVariableID &)>;

    /**
     * Combine a BranchVariableSelector from gcs::variable_order:: with a BranchValueGenerator
     * from gcs::value_order:: to produce a BranchCallback for SolveCallbacks.
     *
     * \ingroup SearchHeuristics
     */
    [[nodiscard]] auto branch_with(BranchVariableSelector, BranchValueGenerator) -> BranchCallback;

    /**
     * Combine two BranchCallback instances, first trying the first instance, and if it returns
     * nullopt, instead trying the second instance.
     *
     * \ingroup SearchHeuristics
     */
    [[nodiscard]] auto branch_sequence(BranchCallback, BranchCallback) -> BranchCallback;

    /**
     * Variable ordering heuristics.
     *
     * \ingroup SearchHeuristics
     */
    namespace variable_order
    {
        /**
         * Used by gcs::variable_order::in_order_of() to implement a variable ordering heuristic
         * that picks the smallest variable wrt this comparator.
         *
         * \ingroup SearchHeuristics
         */
        using VariableComparator = std::function<auto(const CurrentState &, const innards::Propagators &,
            const IntegerVariableID &, const IntegerVariableID &)
                                                     ->bool>;

        /**
         * Branch on the smallest non-assigned variable wrt this comparator.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto in_order_of(const Problem &, VariableComparator) -> BranchVariableSelector;

        /**
         * Branch on the smallest non-assigned variable wrt this comparator.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto in_order_of(std::vector<IntegerVariableID>, VariableComparator) -> BranchVariableSelector;

        /**
         * Branch on the non-assigned variable with smallest domain.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto dom(const Problem &) -> BranchVariableSelector;

        /**
         * Branch on the non-assigned variable with smallest domain.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto dom(std::vector<IntegerVariableID>) -> BranchVariableSelector;

        /**
         * Branch on the non-assigned variable with smallest domain, tie-breaking on highest
         * constraint degree.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto dom_then_deg(const Problem &) -> BranchVariableSelector;

        /**
         * Branch on the non-assigned variable with smallest domain, tie-breaking on highest
         * constraint degree.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto dom_then_deg(std::vector<IntegerVariableID>) -> BranchVariableSelector;

        /**
         * Branch on non-assigned variables in this order.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto in_order(std::vector<IntegerVariableID>) -> BranchVariableSelector;

        /**
         * Branch on the non-assigned variable with the smallest value in its domain.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto with_smallest_value(const Problem &) -> BranchVariableSelector;

        /**
         * Branch on the non-assigned variable with the smallest value in its domain.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto with_smallest_value(std::vector<IntegerVariableID>) -> BranchVariableSelector;

        /**
         * Branch on the non-assigned variable with the largest value in its domain.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto with_largest_value(const Problem &) -> BranchVariableSelector;

        /**
         * Branch on the non-assigned variable with the largest value in its domain.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto with_largest_value(std::vector<IntegerVariableID>) -> BranchVariableSelector;

        /**
         * Branch on a random non-assigned variable.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto random(const Problem &) -> BranchVariableSelector;

        /**
         * Branch on a random non-assigned variable.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto random(std::vector<IntegerVariableID>) -> BranchVariableSelector;
    }

    /**
     * Value ordering heuristics.
     *
     * \ingroup SearchHeuristics
     */
    namespace value_order
    {
        /**
         * Accept then reject the smallest value in the variable's domain.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto smallest_in() -> BranchValueGenerator;

        /**
         * Reject then accept the smallest value in the variable's domain.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto smallest_out() -> BranchValueGenerator;

        /**
         * Iterate from smallest value to largest.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto smallest_first() -> BranchValueGenerator;

        /**
         * Accept then reject the largest value in the variable's domain.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto largest_in() -> BranchValueGenerator;

        /**
         * Reject then accept the largest value in the variable's domain.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto largest_out() -> BranchValueGenerator;

        /**
         * Iterate from largest value to smallest.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto largest_first() -> BranchValueGenerator;

        /**
         * Iterate over values in a random order.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto random() -> BranchValueGenerator;

        /**
         * Accept then reject the median value in the domain.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto median() -> BranchValueGenerator;
    }
}

#endif
