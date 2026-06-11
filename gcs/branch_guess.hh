#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_BRANCH_GUESS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_BRANCH_GUESS_HH

#include <gcs/innards/literal.hh>
#include <gcs/integer.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <variant>

namespace gcs
{
    /**
     * \brief A branching decision to accept or reject a contiguous interval of a
     * variable's domain.
     *
     * `within == true` means "branch var into [lower, upper]"; `within == false`
     * means "branch var out of [lower, upper]" (a genuine disjunctive decision for
     * an interior interval). Kept distinct from Literal so range branching stays out
     * of the general literal-handling code; on the proof side it maps to a single
     * range ("in") literal via NamesAndIDsTracker::need_invar.
     *
     * \ingroup SearchHeuristics
     */
    struct IntegerVariableRangeGuess final
    {
        SimpleIntegerVariableID var;
        Integer lower;
        Integer upper;
        bool within;

        [[nodiscard]] auto operator<=>(const IntegerVariableRangeGuess &) const = default;
    };

    [[nodiscard]] inline auto operator!(const IntegerVariableRangeGuess & g) -> IntegerVariableRangeGuess
    {
        return IntegerVariableRangeGuess{g.var, g.lower, g.upper, ! g.within};
    }

    /**
     * \brief A single branching decision: either an ordinary Literal (a variable
     * condition such as equals / not-equals / bound, or true/false) or an interval
     * accept/reject.
     *
     * A Literal (and hence an IntegerVariableCondition) converts to a BranchGuess
     * implicitly, so existing value-ordering heuristics that `co_yield var == v` keep
     * working unchanged.
     *
     * \ingroup SearchHeuristics
     */
    using BranchGuess = std::variant<innards::Literal, IntegerVariableRangeGuess>;

    [[nodiscard]] inline auto operator!(const BranchGuess & g) -> BranchGuess
    {
        return std::visit([](const auto & x) -> BranchGuess { return ! x; }, g);
    }
}

#endif
