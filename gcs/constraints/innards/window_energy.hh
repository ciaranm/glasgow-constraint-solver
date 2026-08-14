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
     * \brief A task, as the window-energy lemma sees it: a start variable and a
     * length it is guaranteed to run for, plus the per-time proof flags a
     * time-table encoding gives it.
     *
     * The three flag vectors are indexed by <code>t - flags_t_lo</code>, and
     * must be fully reified (so that both their <code>[r]</code> and
     * <code>[f]</code> halves are citable by label) as
     *
     * <ul>
     * <li><code>before[t] &hArr; start &le; t</code></li>
     * <li><code>after[t] &hArr; start &ge; t - length + 1</code>, or, when
     * <code>length_variable</code> is set,
     * <code>after[t] &hArr; start + length_variable &ge; t + 1</code></li>
     * <li><code>active[t] &hArr; before[t] &and; after[t]</code></li>
     * </ul>
     *
     * which is exactly what <code>Cumulative::define_proof_model</code> emits
     * for a constant-length and for a variable-length task respectively.
     *
     * For a variable-length task, <code>length</code> is a value the length is
     * known to be at least, and the lemma counts the task at that: the
     * execution interval <code>[start, start + length_variable)</code> contains
     * <code>[start, start + length)</code>, so activity established for the
     * shorter one is activity all the same. Every derivation is then reason-free
     * in the length exactly when <code>length</code> is its *declared* lower
     * bound; taking a tightened one instead costs a guard (see
     * \ref GuardedWindowEnergy) or a unit RUP (see \ref derive_window_energy).
     *
     * The flag range must cover every time at which the task can be active
     * (i.e. <code>[lb(start), ub(start) + ub(length) - 1]</code> at the time the
     * flags were created): the lemma clips its window to the flag range, and
     * that clipping is only energy-preserving because the task is inactive
     * outside it.
     */
    struct Task
    {
        SimpleIntegerVariableID start;
        Integer length;
        Integer flags_t_lo;
        const std::vector<ProofFlag> & before;
        const std::vector<ProofFlag> & after;
        const std::vector<ProofFlag> & active;
        /// Set iff <code>after</code> is reified on the two-variable
        /// <code>start + length_variable</code>, in which case
        /// <code>length</code> is what the lemma counts the task at and
        /// <code>length_variable &ge; length</code> is what it needs to bridge
        /// back onto <code>start</code>'s order literals.
        std::optional<SimpleIntegerVariableID> length_variable = std::nullopt;
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
     * A variable-length task's <code>after</code> bridge takes one more line
     * (the length's own order literal, which cancels the length out of the
     * flag's reification) and one more term, <code>~[length_variable &ge;
     * length]</code>. That term is discharged once for the whole derivation
     * rather than per time point: at the declared lower bound by the boundary
     * pin need_gevar already wrote down, and anywhere above it by a unit RUP
     * under the reason --- which is why the reason must entail the length bound
     * as well as <code>start_bounds</code>.
     *
     * Returns nullopt when the window is empty after clipping, or when the
     * bound would be zero or less (there is nothing to say, and callers must
     * not cite a line that was never emitted).
     */
    [[nodiscard]] auto derive_window_energy(ProofLogger &, const ReasonLiterals &, const Task &, Integer lo, Integer hi,
        std::pair<Integer, Integer> start_bounds, ProofLevel) -> std::optional<WindowEnergy>;

    /**
     * \brief What derive_guarded_window_energy() proved.
     *
     * The line reads
     *
     * <blockquote>
     * sum of <code>active[t]</code> over the window
     * + <code>low_coeff</code>&middot;<code>~[start &ge; low_guard]</code>
     * + <code>bound</code>&middot;<code>[start &ge; high_guard]</code>
     * + <code>length_coeff</code>&middot;<code>~[length_variable &ge; length]</code>
     * &ge; <code>bound</code>
     * </blockquote>
     *
     * so a citer has to discharge every guard. The first holds for any task the
     * window contains, the second is the negation of a bound push's conclusion,
     * and the third is absent (<code>length_coeff</code> zero) unless the task's
     * length is a variable.
     */
    struct GuardedWindowEnergy
    {
        ProofLine line;
        /// The activity the line establishes once every guard is discharged.
        Integer bound;
        /// The window the sum runs over: the requested one clipped to the flag range.
        Integer lo, hi;
        /// The line carries <code>low_coeff</code> copies of
        /// <code>~[start &ge; low_guard]</code>. A citer whose reason entails
        /// <code>start &ge; low_guard</code> discharges them.
        Integer low_guard, low_coeff;
        /// ... and <code>bound</code> copies of <code>[start &ge; high_guard]</code>,
        /// which is the requested threshold.
        Integer high_guard;
        /// ... and, for a variable-length task, <code>length_coeff</code> copies
        /// of <code>~[length_variable &ge; length_guard]</code>, one per time
        /// point summed. Zero for a constant-length task, whose line has no such
        /// term. A citer whose reason entails the length bound discharges them;
        /// at the declared lower bound the boundary pin does it with no reason
        /// at all.
        Integer length_guard, length_coeff;
    };

    /**
     * \brief Derive the same activity bound as derive_window_energy(), but as a
     * fact about the *model* rather than about the current bounds, so that it
     * can be kept and cited again.
     *
     * derive_window_energy() resolves the order literals its sum leaves over
     * against <code>start_bounds</code>, which makes the line reason-backed and
     * so good for one inference. This weakens them onto two guard literals
     * instead --- every "ends by t" survivor onto <code>[start &ge; low_guard]</code>
     * along the order encoding's own monotonicity, and every "starts after t"
     * survivor at or above <code>high_guard</code> onto that --- leaving a line
     * that holds for every value of the start variable. Emit it once at
     * ProofLevel::Top and every later firing over the same window cites it.
     *
     * The bound is the same one window_energy_bound() predicts for start bounds
     * <code>(low_guard, high_guard - 1)</code>: the guards stand in for the
     * bounds a firing would have had. It is therefore the *clipped* bound
     * whenever a guard falls inside the window, which is what a bound push
     * needs --- the pushed task is the one that does not fit.
     *
     * Which guard the push lands on depends on which way it goes. Raising
     * <code>lb(start)</code> makes <code>high_guard</code> the negated
     * conclusion and <code>low_guard</code> the window start; lowering
     * <code>ub(start)</code> is the mirror, and puts the negated conclusion on
     * <code>low_guard</code>. Either guard may sit inside the survivors' range,
     * and the ones it cannot reach are discharged by their own literal axioms
     * at a unit of the bound each.
     *
     * A variable length is weakened onto a guard of its own for the same
     * reason, and only when it has to be: at the declared lower bound the
     * length term would be paid off by a boundary pin, which is a model fact,
     * but the row is kept across nodes and the caller may well be counting the
     * task at a bound the search has tightened. Carrying the term instead
     * leaves one row that is right at either, and costs its citer one more
     * unit RUP.
     *
     * Costs two more pol lines per surviving order literal than the
     * reason-backed form, all of them inside the part that gets kept.
     *
     * Returns nullopt on an empty clipped window, or when the bound would be
     * zero or less.
     */
    [[nodiscard]] auto derive_guarded_window_energy(
        ProofLogger &, const Task &, Integer lo, Integer hi, Integer low_guard, Integer high_guard, ProofLevel) -> std::optional<GuardedWindowEnergy>;
}

#endif
