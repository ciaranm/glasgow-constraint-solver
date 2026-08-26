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
     */
    [[nodiscard]] auto cumulative_shape_supports_checkpoint_recovery(const std::vector<std::size_t> & active_tasks,
        const std::vector<std::optional<IntegerVariableID>> & presence, const std::vector<IntegerVariableID> & lengths,
        const std::vector<IntegerVariableID> & heights, IntegerVariableID capacity) -> bool;

    /**
     * \brief Whether recover_cumulative_capacity_row can speak about this
     * constraint at all.
     *
     * Asks for the start-checkpoint block to be in the model (see
     * CumulativeEncoding), and for the shapes the recovery has been written
     * for: constant lengths, heights and capacity, and no optional tasks. A
     * variable length moves the diagonal off the row and onto a flag, a
     * variable height replaces a task's coefficient with a bit sum, and a
     * presence adds a conjunct to every activity flag; each is a known
     * extension and none of them is done yet.
     *
     * **A variable capacity is the one whose extension is not merely undone
     * but unwritten**, so what is known about it belongs here rather than in
     * someone's head. The *model* side already handles it --- both the
     * per-time rows and the checkpoint rows move it to the left as a
     * `(-1) * capacity` term when it is not constant. It is the recovery that
     * assumes a constant, in two places, and only one of them is clerical:
     *
     * - `target`, the row being recovered, becomes
     *   `sum h_i * cact_i - capacity <= 0` rather than `... <= capacity`.
     *   Mechanical: the checkpoint rows the derivation adds up carry the same
     *   extra term, so it survives every `pol` unchanged.
     * - `degree = total - capacity` does not survive, and it is load-bearing
     *   twice over. It decides the trivial case (every candidate at once
     *   fits, so the row is a tautology over the flags' own bounds and no
     *   checkpoint is needed), and it is the degree the derivation saturates
     *   at. With the capacity on the left as a bit sum there is no single
     *   constant degree: saturating a row whose right-hand side is a number
     *   and saturating one carrying the capacity's bit coefficients are not
     *   the same operation, and the guard coefficients are computed against
     *   it too.
     *
     * So the open question is precisely that one, and it is a question about
     * saturation rather than about the scheduling argument, which does not
     * change at all. The obvious first thing to try is the trivial case at
     * `total <= lb(capacity)` and the general case relativized on the
     * capacity's bits; nobody has tried it, and this note is not a claim that
     * it works.
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
