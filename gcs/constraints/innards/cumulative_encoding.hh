#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CUMULATIVE_ENCODING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CUMULATIVE_ENCODING_HH

/**
 * \file
 *
 * The switch between `Cumulative`'s OPB encodings. Only one, start-checkpoint,
 * is shipped, and the others exist for test lanes: `cake_pb_cp` derives the
 * shipped one from the `.scp` and would not reproduce another, so a solve
 * that wrote one would carry a model nothing outside this tree agrees with.
 * It lives here, in the innards, rather than beside the constraint, for the
 * reason the proof mutations do (#669): a header a user of the library
 * includes should not advertise it (#1238). The `GCS_CUMULATIVE_ENCODING`
 * environment variable still selects it in any binary, which is what lets a
 * whole fixture set run under another arm, and is a diagnostic only.
 */

namespace gcs::innards
{
    /**
     * \brief Which OPB encoding a Cumulative writes.
     *
     * Unlike \ref CumulativeRules, this *does* change what goes into the OPB.
     * It changes nothing else: the solutions found, the inferences made and
     * the certificates emitted are the same whichever is chosen, because
     * nothing yet derives anything from what the second arm adds.
     *
     * \ingroup Innards
     */
    enum class CumulativeEncoding
    {
        /// The per-time family alone: three fully reified flags per (task,
        /// time point) over each task's possible-active window, and one
        /// capacity row per time point. `O(n x horizon)`, and what every
        /// inference used to cite.
        ///
        /// **Not shipped.** It is kept for one test-only job, and only
        /// Cumulative::with_encoding or the `GCS_CUMULATIVE_ENCODING`
        /// diagnostic selects it: \ref BothRecovering needs the per-time rows
        /// as ground truth. Nothing outside this tree derives it
        /// any more --- `cake_pb_cp` replaced its time-indexed encoder with a
        /// start-checkpoint one (CakePB-dev a402078, 2026-09-19) --- so the
        /// `scp_chain_cumulative*` cases that used to be pinned to it now check
        /// the shipped encoding against cake's.
        TimeIndexed,

        /// Both families in the model, and then derive every per-time capacity
        /// row from the start-checkpoint rows and check it against the row the
        /// model still carries beside it.
        ///
        /// The development arm for the middle of #780, and the answer to "did
        /// the recovery derive the right thing". A recovery that is *invalid*
        /// fails where it is emitted; a recovery that is valid but derives the
        /// *wrong* row --- citing the neighbouring checkpoint, say --- emits a
        /// perfectly good line, and only the implication check against the
        /// model's own row rejects it. So the two encodings standing side by
        /// side buy something here that neither buys alone.
        ///
        /// Deliberately eager, which the recovery itself is not meant to be:
        /// this recovers every row rather than the ones a search cites, so it
        /// is `O(horizon)` work in the proof and belongs in a test lane rather
        /// than in a solve. It does nothing for a Cumulative the recovery
        /// cannot yet speak about --- see
        /// innards::cumulative_checkpoint_recovery_applies.
        BothRecovering,

        /// The start-checkpoint family alone, with the per-time block not
        /// written at all: per ordered pair of active tasks, flags saying
        /// whether one is running when the other starts, and one capacity row
        /// per task. `6n(n-1) + n` rows and **no dependence on the horizon**.
        ///
        /// **This is the encoding Cumulative ships, and the only one.** Two
        /// would mean cake had to reproduce our per-constraint choice exactly,
        /// and a disagreement between the two models shows up as a rejected
        /// proof rather than as an error.
        ///
        /// Every rule cites a per-time capacity row *recovered in the proof*
        /// rather than read from the model; see
        /// innards::recover_cumulative_capacity_row. There is no shape to fall
        /// back for, because a Cumulative the recovery cannot speak about never
        /// reaches the encoder: no active task makes `prepare()` return false,
        /// and a height whose bits cannot be cited --- a view --- makes it
        /// throw.
        StartCheckpoint
    };

}

#endif
