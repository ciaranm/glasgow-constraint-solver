#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LOGGER_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LOGGER_FWD_HH

#include <gcs/innards/proofs/proof_line-fwd.hh>

namespace gcs::innards
{
    class ProofLogger;

    /**
     * Controls deletions of constraints inside a proof. Items written at level
     * Current are erased on backtrack, and items in Temporary are erased at
     * the end of the current propagation section.
     *
     * \ingroup Innards
     */
    enum class ProofLevel
    {
        Current,
        Top,
        Temporary,
        /**
         * As Top --- kept for the whole proof --- and additionally moved into
         * VeriPB's core set with a `core id`.
         *
         * Used for one thing: a variable's *encoding*.
         *
         * The deletion check that lets a `solx` blocking clause go away has to
         * get from the preserved variables the clause is written over (a
         * variable's bits) to the atoms the backtrack clause justifying it is
         * written over (its order, equality and interval literals), and only
         * core constraints count towards that check. The rows that make that
         * crossing are a variable's encoding. They are OPB rows, hence already
         * core, for anything that existed when the model was written; a literal
         * first needed partway through the search is defined by a `red` in the
         * proof instead, and without this would land in the derived set where
         * the check cannot see it.
         *
         * Emitted by NamesAndIDsTracker, and only by it: the line is drawn
         * structurally, at a variable's encoding rather than at whatever a check
         * turns out to need, so a propagator's standing lemma stays derived.
         * See dev_docs/solution-clause-deletion.md.
         */
        TopAndCore
    };
}

#endif
