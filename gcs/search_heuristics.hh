#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SEARCH_HEURISTICS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SEARCH_HEURISTICS_HH

#include <gcs/innards/state-fwd.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/variable_weighting.hh>

#include <cstdint>
#include <functional>
#include <optional>
#include <vector>

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
     * A variable-ordering heuristic that needs per-search setup before it can
     * select: given a search's Problem, State, and Propagators, it does any
     * one-time setup (for example a stateful heuristic constructing its weights
     * and attaching itself as a conflict observer) and returns the
     * BranchVariableSelector to branch with. Called once per search; in a
     * parallel search, once per thread with that thread's own State and
     * Propagators. A stateless ordering simply ignores the arguments and returns
     * its selector.
     *
     * Currently only gcs::variable_order::dom_wdeg() returns one of these; the
     * other gcs::variable_order:: orderings still return a BranchVariableSelector
     * directly, pending a later migration to this shape.
     *
     * \ingroup SearchHeuristics
     */
    using BranchVariableHeuristic = std::function<BranchVariableSelector(
        const Problem &, innards::State &, innards::Propagators &)>;

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
         * \brief dom/wdeg: branch on the non-assigned variable minimising
         * dom(x)/W(x), where W(x) is the weighted degree from a dynamic
         * constraint weighting (classic dom/wdeg: Boussemart, Hemery, Lecoutre,
         * Sais, ECAI 2004).
         *
         * Returns a BranchVariableHeuristic, not a bare selector: at search start
         * it constructs a ClassicDomWDeg weighting (one weight per constraint,
         * initialised to 1, bumped on each domain wipeout), attaches it as the
         * Propagators' conflict observer, and returns the selector. Weights start
         * uniform, so at the root the heuristic orders by dom(x)/degree(x) and it
         * specialises towards hard constraints as conflicts accumulate. Ties are
         * broken on highest constraint degree, and a variable with W(x)=0 (in no
         * constraint with two or more unassigned variables) is least preferred.
         *
         * An optional initial WeightingState seeds the weights --- for carrying
         * weights across searches or injecting proof-mined weights. Value
         * ordering is chosen separately, as usual via gcs::branch_with().
         *
         * \ingroup SearchHeuristics
         * \sa WeightingState
         */
        [[nodiscard]] auto dom_wdeg(const Problem &,
            std::optional<WeightingState> initial = std::nullopt) -> BranchVariableHeuristic;

        /**
         * \brief dom/wdeg over an explicit list of variables.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::variable_order::dom_wdeg(const Problem &, std::optional<WeightingState>)
         */
        [[nodiscard]] auto dom_wdeg(std::vector<IntegerVariableID>,
            std::optional<WeightingState> initial = std::nullopt) -> BranchVariableHeuristic;

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
         * Branch on a random non-assigned variable, seeded non-deterministically.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto random(const Problem &) -> BranchVariableSelector;

        /**
         * Branch on a random non-assigned variable, seeded non-deterministically.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto random(std::vector<IntegerVariableID>) -> BranchVariableSelector;

        /**
         * Branch on a random non-assigned variable, with an explicit seed for
         * reproducible debugging.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto random(const Problem &, std::uint_fast32_t seed) -> BranchVariableSelector;

        /**
         * Branch on a random non-assigned variable, with an explicit seed for
         * reproducible debugging.
         *
         * \ingroup SearchHeuristics
         * \sa gcs::branch_with()
         */
        [[nodiscard]] auto random(std::vector<IntegerVariableID>, std::uint_fast32_t seed) -> BranchVariableSelector;
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
         * Split domains in half, taking lower half first.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto split_smallest_first() -> BranchValueGenerator;

        /**
         * Split domains in half, taking upper half first.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto split_largest_first() -> BranchValueGenerator;

        /**
         * Split domains in half, taking a random half first.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto split_random() -> BranchValueGenerator;

        /**
         * Split domains in half, taking a random half first, with an explicit
         * seed for reproducible debugging.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto split_random(std::uint_fast32_t seed) -> BranchValueGenerator;

        /**
         * Iterate over values in a random order.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto random() -> BranchValueGenerator;

        /**
         * Iterate over values in a random order, with an explicit seed for
         * reproducible debugging.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto random(std::uint_fast32_t seed) -> BranchValueGenerator;

        /**
         * Reject a random value, then accept it. This is a silly heuristic for solving
         * problems, but an interesting one for testing.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto random_out() -> BranchValueGenerator;

        /**
         * Reject a random value, then accept it, with an explicit seed for
         * reproducible debugging.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto random_out(std::uint_fast32_t seed) -> BranchValueGenerator;

        /**
         * Accept then reject the median value in the domain.
         *
         * \ingroup SearchHeuristics
         */
        [[nodiscard]] auto median() -> BranchValueGenerator;
    }
}

#endif
