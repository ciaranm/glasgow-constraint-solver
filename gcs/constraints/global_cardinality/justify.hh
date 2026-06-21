#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_JUSTIFY_HH

#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>
#include <vector>

namespace gcs::innards
{
    // The two count lines for each cover value, {Sum_i x_{i=v} <= c_v,
    // Sum_i x_{i=v} >= c_v}, as emitted by the proof model.
    using GCCCountLines = std::vector<std::pair<std::optional<ProofLine>, std::optional<ProofLine>>>;

    /**
     * \brief Emit the capacity-cut aggregate for a set W of cover values.
     *
     * Sums, over each value v in W, the count line Sum_i x_{i=v} <= c_v and (for
     * a non-constant count) the defining implication of c_v <= ub_v, plus an
     * at-least-one over its domain for each confined variable (a variable whose
     * domain lies within the W values). The result is
     *   Sum_{i not confined, v in W} x_{i=v} <= cap - |confined|,
     * cap = Sum_{v in W} ub_v. When the cut is saturated (|confined| == cap) the
     * right-hand side is 0, so a wrapping RUP under \ref gcc_capacity_reason
     * closes any pruning of a W value from a non-confined variable (or a
     * contradiction).
     */
    auto emit_gcc_capacity_pol(ProofLogger &, const State &,
        const std::vector<IntegerVariableID> & vars, const std::vector<Integer> & values,
        const std::vector<IntegerVariableID> & counts, const GCCCountLines & count_lines,
        const std::vector<std::size_t> & cut_values, const std::vector<IntegerVariableID> & confined) -> void;

    auto gcc_capacity_reason(const State &, const std::vector<Integer> & values,
        const std::vector<IntegerVariableID> & counts, const std::vector<std::size_t> & cut_values,
        const std::vector<IntegerVariableID> & confined) -> ReasonLiterals;

    /**
     * \brief Emit the demand-cut aggregate (dual of the capacity one) for a set
     * W of cover values.
     *
     * Sums, over each value v in W, the count line Sum_i x_{i=v} >= c_v and (for
     * a non-constant count) the defining implication of c_v >= lb_v, plus an
     * at-most-one over W for each potential variable (one that can take a W
     * value). If `pruned_var` is given it gets an at-most-one over W together
     * with the extra value `cut_values`-external value index `pruned_value`. The
     * result is Sum_{i not potential, v in W} x_{i=v} >= demand - |potential|;
     * a wrapping RUP under \ref gcc_demand_reason closes the pruning/contradiction.
     */
    auto emit_gcc_demand_pol(ProofLogger &, const State &,
        const std::vector<IntegerVariableID> & vars, const std::vector<Integer> & values,
        const std::vector<IntegerVariableID> & counts, const GCCCountLines & count_lines,
        const std::vector<std::size_t> & cut_values, const std::vector<IntegerVariableID> & potential,
        std::optional<IntegerVariableID> pruned_var, std::optional<Integer> pruned_value) -> void;

    auto gcc_demand_reason(const State &, const std::vector<IntegerVariableID> & vars,
        const std::vector<Integer> & values, const std::vector<IntegerVariableID> & counts,
        const std::vector<std::size_t> & cut_values, const std::vector<IntegerVariableID> & potential) -> ReasonLiterals;
}

#endif
