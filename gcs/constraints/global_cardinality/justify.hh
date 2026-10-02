#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_JUSTIFY_HH

#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <algorithm>
#include <iterator>
#include <optional>
#include <utility>
#include <vector>

namespace gcs::innards
{
    // The two count lines for each cover value, {Sum_i x_{i=v} <= c_v,
    // Sum_i x_{i=v} >= c_v}, as emitted by the proof model.
    using GCCCountLines = std::vector<std::pair<std::optional<ProofLine>, std::optional<ProofLine>>>;

    /**
     * \brief Make a Hall inference whose reason and justification both read the
     * state it was decided in, not the state after it.
     *
     * The single-literal infer() pushes the literal first and then runs the
     * justification, and a LazyReasonOver is materialised after the push too
     * (snapshot_reason, in inference_tracker.hh). The Hall reasons and pols read
     * the domains of other positions and the counts' bounds, and when the array
     * holds a variable and a view of it, or a count is itself one of the
     * variables or a view of another count, the push moves those too: the reason
     * could come out naming the conclusion itself, or the pol could state a
     * bound the reason does not, and VeriPB rejected the proof (issue #1191).
     *
     * So when a proof is being written, build the reason now and go through
     * infer_all(), which emits the justification's steps before it pushes
     * anything and closes each literal with a RUP under that same reason.
     * Without a logger nothing is logged and the reason is never read, so this
     * is the plain infer() with no reason, exactly as before.
     */
    template <typename Inference_, typename Emit_, typename Hint_, typename BuildReason_>
    auto infer_hall_before_push(Inference_ & inference, ProofLogger * const logger, const Literal & lit, const JustifyExplicitly<Emit_, Hint_> & why,
        BuildReason_ && build_reason) -> void
    {
        if (logger && inference.want_reasons())
            inference.infer_all(logger, std::vector<Literal>{lit}, why, Reason{ExplicitReason{build_reason()}});
        else
            inference.infer(logger, lit, why, Reason{NoReason{}});
    }

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
    auto emit_gcc_capacity_pol(ProofLogger &, const State &, const std::vector<IntegerVariableID> & vars, const std::vector<Integer> & values,
        const std::vector<IntegerVariableID> & counts, const GCCCountLines & count_lines, const std::vector<std::size_t> & cut_values,
        const std::vector<IntegerVariableID> & confined) -> void;

    auto gcc_capacity_reason(const State &, const std::vector<Integer> & values, const std::vector<IntegerVariableID> & counts,
        const std::vector<std::size_t> & cut_values, const std::vector<IntegerVariableID> & confined) -> ReasonLiterals;

    /**
     * \brief Append "this variable is confined to the hall set" to a reason, as
     * its two bounds plus one range condition per run of values it cannot take.
     *
     * \p hall_begin / \p hall_end are the hall set's values in ascending order;
     * both arms hold theirs that way already (a slice of the sorted cover in the
     * bounds propagator, a std::set in the GAC one).
     *
     * The facts stated are the same ones the per-value spelling stated, and they
     * are what turns each confined variable's at-least-one into an at-least-one
     * *over the hall set* in the capacity pol: every term outside the set has to
     * be falsified for that aggregate to come out. What changes is the count. A
     * confined variable's domain lies inside the hall set, so both of its bounds
     * are hall values and every value it cannot take between them is a gap
     * between two consecutive hall values -- so there are at most |H| - 1 runs,
     * where walking the values cost ub - lb, and that is the *span* of the cover
     * the model chose rather than anything about the variable (issue #936).
     *
     * **Why a range literal is as strong here as the disequalities it replaces,
     * and what would break that.** The closure RUP has to falsify each individual
     * `x[j=s]` term the AL1 contributes for s in a gap. It can, because the AL1 is
     * built over the definition range and so has already shattered every gap into
     * singleton eq atoms, and `link_immediate_containment` emits `~[j=s] \/ [j in
     * g]` for each eq atom a range literal contains -- so unit propagation
     * descends the containment tree and zeroes them one by one. It is *not* the
     * threshold crossing dev_docs/large-domains.md warns about under "Getting a
     * range removal past the checker"; that is a different step.
     *
     * The consequence is a coupling worth stating: **if the AL1 stops naming every
     * value of the definition range (which is what issue #939 is about), these
     * range literals stop propagating and the closure fails.** The shattering and
     * the range spelling have to move together. #939's own suggested fix -- a
     * per-firing at-least-one over the hall set, stated under exactly these
     * literals -- does move them together, and makes this list the literal list of
     * that line rather than a separate patch.
     */
    template <typename Iter_>
    auto append_confined_to_hall_reason(const State & state, const IntegerVariableID & var, Iter_ hall_begin, Iter_ hall_end, ReasonLiterals & r)
        -> void
    {
        auto [v_lo, v_hi] = state.bounds(var);
        for (auto it = hall_begin; it != hall_end; ++it) {
            auto next = std::next(it);
            if (next == hall_end)
                break;
            // Clipped to the variable's bounds, exactly as the per-value loop
            // was. Both bounds are themselves hall values, so this only drops
            // gaps that lie wholly outside them.
            auto lo = std::max(*it + 1_i, v_lo);
            auto hi = std::min(*next - 1_i, v_hi);
            if (lo <= hi)
                r.emplace_back(not_in_range(var, lo, hi));
        }
        r.emplace_back(var >= v_lo);
        r.emplace_back(var <= v_hi);
    }

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
    auto emit_gcc_demand_pol(ProofLogger &, const State &, const std::vector<IntegerVariableID> & vars, const std::vector<Integer> & values,
        const std::vector<IntegerVariableID> & counts, const GCCCountLines & count_lines, const std::vector<std::size_t> & cut_values,
        const std::vector<IntegerVariableID> & potential, std::optional<IntegerVariableID> pruned_var, std::optional<Integer> pruned_value) -> void;

    auto gcc_demand_reason(const State &, const std::vector<IntegerVariableID> & vars, const std::vector<Integer> & values,
        const std::vector<IntegerVariableID> & counts, const std::vector<std::size_t> & cut_values, const std::vector<IntegerVariableID> & potential)
        -> ReasonLiterals;
}

#endif
