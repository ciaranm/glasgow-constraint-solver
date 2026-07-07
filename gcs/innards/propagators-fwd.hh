#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_FWD_HH

namespace gcs::innards
{
    /**
     * Should a propagator be called again, or is it guaranteed it cannot
     * perform any more inference?
     *
     * The values form a strength ladder: Enable promises nothing,
     * EnableButIdempotent adds a claim about this run only, and
     * DisableUntilBacktrack disables the propagator for the whole subtree.
     *
     * \ingroup Innards
     */
    enum class PropagatorState
    {
        /**
         * Keep the propagator registered; re-running it might infer more even
         * if nothing else has changed since.
         */
        Enable,

        /**
         * Keep the propagator registered, but this run reached its own
         * fixpoint: re-running this propagator immediately, against the
         * domains exactly as this run left them, would infer nothing and not
         * contradict. The propagation queue uses this to skip re-waking the
         * propagator from its own inferences; changes made by any other
         * propagator wake it as usual. Because propagators are monotone the
         * per-node fixpoint (and so the search tree) is unchanged, though
         * work can shift by a round, so inference attribution -- and with it
         * proof line order and the effectful-propagation split -- can differ
         * from the never-claiming engine.
         *
         * The claim is per-run: a propagator whose algorithm is only
         * sometimes idempotent claims only on the runs where it is true.
         * Most propagators are only idempotent when no two scope positions
         * alias the same underlying variable (directly or through a view), so
         * a claiming propagator must register its Triggers 1:1 with its scope
         * positions — Propagators::install detects aliased trigger scopes and
         * silently ignores claims from such propagators — or guarantee its
         * own de-aliasing. A wrong claim silently under-propagates or, for
         * constraints whose feasibility is enforced only by repeated
         * propagation, is unsound: set GCS_CHECK_IDEMPOTENT_CLAIMS (on by
         * default in the constraint test harness) to have every honoured
         * claim checked by an immediate re-run.
         */
        EnableButIdempotent,

        /**
         * The constraint is entailed within this whole subtree: disable the
         * propagator at this search node and every descendant, re-enabling on
         * backtrack above it.
         */
        DisableUntilBacktrack
    };

    class Propagators;
}

#endif
