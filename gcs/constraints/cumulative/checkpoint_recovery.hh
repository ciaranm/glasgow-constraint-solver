#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_CHECKPOINT_RECOVERY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_CHECKPOINT_RECOVERY_HH

#include <gcs/constraints/cumulative/propagate.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/integer.hh>

#include <cstddef>
#include <map>
#include <optional>
#include <tuple>
#include <utility>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief What the start-checkpoint recovery keeps between calls.
     *
     * Two kinds of thing. The order facts --- that the start order is total,
     * and that it is transitive --- say nothing about a time point, so they are
     * derived once for the constraint and shared by every recovery. The
     * recovered rows are keyed on the time point, which is the whole cache key:
     * every rule in the time-table family cites the row for `t` and nothing
     * finer, so a row derived for one citer serves all of them.
     *
     * Everything in here lives at ProofLevel::Top and is reason-free, so
     * nothing in it is invalidated by backtracking.
     *
     * \ingroup Innards
     */
    struct CheckpointRecoveryCache
    {
        /// `sb_{i,j} \/ sb_{j,i}`, for `i < j`.
        std::map<std::pair<std::size_t, std::size_t>, ProofLine> totality;

        /// `sb_{a,b} /\ sb_{b,c} -> sb_{a,c}`.
        std::map<std::tuple<std::size_t, std::size_t, std::size_t>, ProofLine> transitivity;

        /// The recovered capacity row for each time point asked for.
        std::map<Integer, ProofLine> recovered;
    };

    /**
     * \brief Whether the recovery could speak about a Cumulative of this
     * *shape*, without asking whether the checkpoint block is in the model.
     *
     * The half of \ref cumulative_checkpoint_recovery_applies that can be
     * answered before any row has been written, which is what
     * CumulativeEncoding::StartCheckpoint needs: it has to decide whether to
     * emit the time-indexed block at all, and it makes that decision while
     * building the model. Splitting it keeps one statement of what the shape
     * requirement is, rather than a copy in the encoder that could drift from
     * the one the recovery enforces.
     *
     * It now turns down only a Cumulative with no active task, every actual
     * *shape* --- optional tasks, variable lengths, variable heights, a
     * variable capacity --- having been brought in. The presence, length,
     * height and capacity parameters stay in the signature anyway: the
     * question is "could the recovery speak about a Cumulative of this shape",
     * the answer has merely stopped depending on them, and a caller should not
     * have to know that. Keeping them also means the next shape the encoder
     * learns to write has somewhere to be declined from.
     */
    [[nodiscard]] auto cumulative_shape_supports_checkpoint_recovery(const std::vector<std::size_t> & active_tasks,
        const std::vector<std::optional<IntegerVariableID>> & presence, const std::vector<IntegerVariableID> & lengths,
        const std::vector<IntegerVariableID> & heights, IntegerVariableID capacity) -> bool;

    /**
     * \brief Whether recover_cumulative_capacity_row can speak about this
     * constraint at all.
     *
     * Asks for the start-checkpoint block to be in the model (see
     * CumulativeEncoding). That is now the whole of it: the recovery speaks
     * about every shape the encoder can write, so the shape half of this
     * question (\ref cumulative_shape_supports_checkpoint_recovery) only
     * turns down a Cumulative with no active task, which has no checkpoint row
     * to recover from.
     *
     * What each of the four shapes took, since knowing which were hard is
     * worth more than knowing they are done:
     *
     * - **An optional task** and **a variable length** took the same one
     *   change, on the diagonal. Give a task a presence or a variable length
     *   and the encoder mints `sact_{j,j}` and puts `j`'s own height on the
     *   checkpoint row; with a constant length and no presence it folds that
     *   height into the right hand side instead and there is no flag. So the
     *   recovery pins the diagonal where the flag is there and axiomatises it
     *   where it is not. Nothing off the diagonal changed: `cact` and `sact`
     *   both carry the presence conjunct, and `sa_{i,j}` already reified on
     *   `s_i + l_i` directly when the length varied.
     * - **A variable height** needed an argument. It is a coefficient on
     *   neither flag --- the checkpoint row carries the pair's bit-linearised
     *   contribution and the target carries the per-time one --- so `~cact`
     *   stops being the load term and becomes a guard residue, and a residue
     *   left on a case clause is a literal the scan cannot resolve away. The
     *   swap therefore goes through a fact that holds either side of `cact`,
     *   for two different reasons, and is proved by a case split relativized
     *   on a flag of its own. See the comment at the swap.
     * - **A variable capacity** turned out to be nearly free, and an earlier
     *   version of this note was wrong about why it would not be. It said
     *   `degree = total - capacity` was "the degree the derivation saturates
     *   at" and that the guard coefficients were computed against it. Neither
     *   is so: `degree` was only ever the test for the trivial case. The
     *   capacity itself needs no special handling, because it cancels between
     *   the checkpoint row and the target's own reverse half exactly as the
     *   load does. All it cost was carrying the row in the encoder's own two
     *   forms, and giving up the trivial-case shortcut where there is no
     *   single number to compare against.
     *
     * The lesson in that last one is worth keeping: the argument was about
     * *scheduling*, and it never mentioned the capacity's constancy. Guessing
     * that PB arithmetic would be the obstacle, without following the constant
     * through the code to see what it actually reached, produced a confident
     * note that pointed at the wrong thing.
     */
    [[nodiscard]] auto cumulative_checkpoint_recovery_applies(const CumulativeInputs & inputs, const ProofLogger & logger) -> bool;

    /**
     * \brief Derive the capacity row for time point `t` from the
     * start-checkpoint rows, at ProofLevel::Top and reason-free.
     *
     * The argument: let `j` be the candidate with the largest start among those
     * that have started by `t`. Every candidate `i` active at `t` has
     * `s_i <= t <= s_j` and `s_i + l_i >= t + 1 >= s_j + 1`, so it is active
     * when `j` starts, and `j`'s checkpoint row caps exactly the load at `t`.
     * Note `j` need not itself be active at `t` --- only started --- which is
     * what keeps the case split off the active set.
     *
     * Nullopt when \ref cumulative_checkpoint_recovery_applies says no, or when
     * no task can be active at `t` at all (there is then no row to recover, and
     * the model has none either).
     *
     * See dev_docs/cumulative-proof-logging.md for the step-by-step derivation
     * and what it costs.
     */
    [[nodiscard]] auto recover_cumulative_capacity_row(
        ProofLogger & logger, const CumulativeInputs & inputs, CheckpointRecoveryCache & cache, Integer t) -> std::optional<ProofLine>;

    /**
     * \brief Recover every capacity row the model wrote, and check each against
     * the row still standing beside it.
     *
     * The differential CumulativeEncoding::BothRecovering exists for. Deriving
     * a row that is *invalid* fails inside the recovery, loudly; deriving a
     * valid row that is not the one the case wanted --- citing the neighbouring
     * checkpoint, say --- produces a perfectly good line, and only asking
     * whether it implies the model's own row catches that.
     *
     * Deliberately eager, which the recovery is not meant to be: the point here
     * is to check every row, not to pay for only the ones a search cites. No-op
     * when \ref cumulative_checkpoint_recovery_applies says no.
     */
    auto check_recovered_cumulative_capacity_rows(ProofLogger & logger, const CumulativeInputs & inputs, CheckpointRecoveryCache & cache) -> void;
}

#endif
