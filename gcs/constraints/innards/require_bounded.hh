#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_REQUIRE_BOUNDED_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_REQUIRE_BOUNDED_HH

#include <gcs/expression.hh>
#include <gcs/extensional.hh>
#include <gcs/innards/literal.hh>
#include <gcs/integer.hh>
#include <gcs/reification.hh>
#include <gcs/variable_condition.hh>

#include <vector>

namespace gcs::innards
{
    /**
     * \name Range checks for constraint parameters.
     *
     * Each throws IntegerOverflow if any Integer in the parameter lies outside
     * Integer::min_bounded_value() .. Integer::max_bounded_value(), the range
     * every input to the solver must lie in (dev_docs/integer-ranges.md). A
     * constraint calls these on its parameters in its constructor. \a what
     * names the parameter in the message.
     *
     * A condition's value may also be one past the top of the range, because
     * `x <= v` is stored as `x < v + 1` and `x > v` as `x >= v + 1`: those
     * are the values an in-range `v` produces.
     */
    ///@{
    auto require_bounded(const std::vector<Integer> & values, const char * what) -> void;
    auto require_bounded(const std::vector<std::vector<Integer>> & values, const char * what) -> void;
    auto require_bounded(const WeightedSum & sum, const char * what) -> void;
    auto require_bounded(const ExtensionalTuples & tuples, const char * what) -> void;
    auto require_bounded(const IntegerVariableCondition & cond, const char * what) -> void;
    auto require_bounded(const Literal & lit, const char * what) -> void;
    auto require_bounded(const Literals & lits, const char * what) -> void;
    auto require_bounded(const ReificationCondition & cond, const char * what) -> void;
    ///@}
}

#endif
