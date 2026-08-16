#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_TASK_PRESENCE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_TASK_PRESENCE_HH

#include <gcs/variable_id.hh>

#include <optional>
#include <string_view>

/**
 * \file
 *
 * What a scheduling constraint's `presences` argument means for one task, in
 * one place. `Cumulative` and `Disjunctive` both take optional tasks, they
 * encode them differently (a conjunct on a per-time activity flag; a disjunct
 * on a pairwise separation clause), and they must nonetheless agree exactly on
 * *which* presences resolve away at prepare() time and which survive into the
 * OPB --- so that rule lives here rather than once per constraint.
 */

namespace gcs::innards
{
    /**
     * \brief What a scheduling constraint's presence argument for one task
     * comes to: what its encoding has to be conditioned on, and whether the
     * task is there at all.
     *
     * \sa task_presence
     *
     * \ingroup Innards
     */
    struct TaskPresence
    {
        /// The {0, 1} variable the task's encoding has to carry --- Cumulative
        /// as a third conjunct on each activity flag, Disjunctive as a disjunct
        /// on each separation clause the task appears in --- or nullopt when the
        /// task is unconditionally present and the encoding is the one a
        /// constraint posted without presences at all would write.
        std::optional<IntegerVariableID> literal;

        /// Whether the task was posted as constantly absent, in which case it is
        /// left out of the constraint altogether: no flags, no terms in any row,
        /// and nothing may cite it.
        bool never_present = false;
    };

    /**
     * \brief How a scheduling constraint resolves the presence argument it was
     * posted with for one task, given that argument (nullopt for a constraint
     * posted without presences at all).
     *
     * Only a *constant* argument resolves away: a variable presence keeps its
     * literal even when its domain is already a singleton, because the encoding
     * has to say what it means without appealing to a domain the OPB does not
     * record. That is what makes "post every presence as the constant 1" produce
     * a byte-identical OPB to not passing presences at all, which both
     * constraints' tests check.
     *
     * Shared, and deliberately so, for two independent reasons. A *derived*
     * Cumulative pins its donor's activity flags, so it has to reach exactly the
     * same verdict about which of them carry a presence literal as the donor did
     * when it built them; and `Disjunctive` and `Cumulative` are two encodings
     * of overlapping problems that a modeller may swap between, so a presence
     * argument one of them resolves away and the other does not would be a
     * difference in meaning with nothing recording it.
     *
     * \param constraint_name what to call the constraint in the rejection
     * message, since the modeller met this argument under that name and not
     * under this function's.
     *
     * \throws InvalidProblemDefinitionException if a constant argument is
     * outside {0, 1}. A variable one is range-checked by the caller, at
     * prepare() time, where its domain is first available.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto task_presence(const std::optional<IntegerVariableID> & posted, std::string_view constraint_name) -> TaskPresence;
}

#endif
