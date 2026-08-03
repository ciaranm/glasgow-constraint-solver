#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_WINDOW_ENERGY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_WINDOW_ENERGY_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/reason.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>
#include <vector>

namespace gcs::innards::window_energy
{
    /**
     * \brief A task, as the window-energy lemma sees it: a start variable with a
     * constant duration, plus the per-time proof flags a time-table encoding
     * gives it.
     *
     * The three flag vectors are indexed by <code>t - flags_t_lo</code>, and
     * must be fully reified (so that both their <code>[r]</code> and
     * <code>[f]</code> halves are citable by label) as
     *
     * <ul>
     * <li><code>before[t] &hArr; start &le; t</code></li>
     * <li><code>after[t] &hArr; start &ge; t - length + 1</code></li>
     * <li><code>active[t] &hArr; before[t] &and; after[t]</code></li>
     * </ul>
     *
     * which is exactly what <code>Cumulative::define_proof_model</code> emits.
     *
     * The flag range must cover every time at which the task can be active
     * (i.e. <code>[lb(start), ub(start) + length - 1]</code> at the time the
     * flags were created): the lemma clips its window to the flag range, and
     * that clipping is only energy-preserving because the task is inactive
     * outside it.
     */
    struct ConstantLengthTask
    {
        SimpleIntegerVariableID start;
        Integer length;
        Integer flags_t_lo;
        const std::vector<ProofFlag> & before;
        const std::vector<ProofFlag> & after;
        const std::vector<ProofFlag> & active;
    };

    /**
     * \brief What derive_window_energy() proved.
     */
    struct WindowEnergy
    {
        /// The derived line: <code>sum of active[t] for t in [lo, hi) &ge; bound</code>.
        ProofLine line;
        /// The bound the line establishes. Always at least 1 when a line exists.
        Integer bound;
        /// The window the sum actually runs over: the requested window clipped
        /// to the task's flag range.
        Integer lo, hi;
    };

    /**
     * \brief How much activity a window-energy derivation over this window
     * would establish, without emitting anything.
     *
     * This is the minimum, over every start position still allowed by
     * <code>start_bounds</code>, of the overlap between the task's execution
     * interval and the window --- i.e. the strongest bound the lemma can
     * certify. Callers use it to decide whether a window is worth an emission,
     * and tests use it as the oracle the emitted claim must match.
     */
    [[nodiscard]] auto window_energy_bound(
        Integer length, Integer flags_t_lo, std::size_t flags_size, Integer lo, Integer hi, std::pair<Integer, Integer> start_bounds) -> Integer;

    /**
     * \brief Derive a lower bound on a task's activity inside a time window.
     *
     * Under the reason context (which must entail <code>start_bounds</code>),
     * derives
     *
     * <blockquote>
     * sum of <code>active[t]</code> for <code>t</code> in the window &ge; bound
     * </blockquote>
     *
     * in O(window width) proof steps, and returns the line. The derivation is
     * three steps per time point --- two saturated two-line pols bridging
     * <code>before</code> / <code>after</code> to the start variable's order
     * literals, and one combining them with the <code>active</code> AND-gate
     * --- followed by one pol summing them, into which the order literals
     * telescope: the sum's <code>start</code> terms cancel exactly, in the
     * same way the <code>end</code> bridge lemma's operand bits do.
     *
     * Returns nullopt when the window is empty after clipping, or when the
     * bound would be zero or less (there is nothing to say, and callers must
     * not cite a line that was never emitted).
     */
    [[nodiscard]] auto derive_window_energy(ProofLogger &, const ReasonLiterals &, const ConstantLengthTask &, Integer lo, Integer hi,
        std::pair<Integer, Integer> start_bounds, ProofLevel) -> std::optional<WindowEnergy>;
}

#endif
