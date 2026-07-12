#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_CONFLICT_OBSERVER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_CONFLICT_OBSERVER_HH

#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Watches propagation for conflicts (domain wipeouts) as they
     * happen, so that a search heuristic can attribute each wipeout to the
     * constraint --- and, later, the specific Reason --- that caused it.
     *
     * A borrowed observer is attached to the Propagators for the duration of a
     * search (Propagators::set_conflict_observer). Whenever a propagator raises
     * a contradiction, Propagators::propagate notifies the observer exactly once
     * with the failing constraint and its scope. This is the write side of the
     * dom/wdeg weighting seam (issue #315, Stage 0): the weighting value object
     * will implement this interface. It is deliberately minimal and carries no
     * query API of its own --- the brancher reads back weights by another path.
     *
     * \ingroup Innards
     */
    class ConflictObserver
    {
    public:
        virtual ~ConflictObserver() = default;

        /**
         * \brief Called when a propagator wipes out a domain.
         *
         * \param constraint_index the dense constraint index of the failing
         *   propagator, as from Propagators::constraint_index_of_propagator.
         * \param scope the failing propagator's scope, as from
         *   Propagators::scope_of_propagator: its variables, with views
         *   resolved to the underlying simple variable and duplicates removed.
         * \param reason the declarative reason carried by the contradiction. The
         *   optional is engaged whenever a contradiction occurred, but the Reason
         *   it holds may itself be NoReason when the propagator supplied none; an
         *   observer that wants its literals materialises it against \p state.
         * \param state the current state, for querying variable domains.
         */
        virtual auto note_conflict(int constraint_index, const std::vector<SimpleIntegerVariableID> & scope, const std::optional<Reason> & reason,
            const State & state) -> void = 0;

        /**
         * \brief Called by the search at each restart boundary, so a weighting
         * scheme can decay or smooth its scores.
         *
         * This is how solve_with() reaches the live weighting (which it does not
         * own) to signal a restart: the weighting is attached here as the
         * conflict observer, so the restart hook rides the same seam. The default
         * does nothing; VariableWeighting forwards to its scheme.
         */
        virtual auto on_restart() -> void
        {
        }
    };
}

#endif
