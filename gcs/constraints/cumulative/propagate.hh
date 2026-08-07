#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_PROPAGATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_PROPAGATE_HH

#include <gcs/constraint_id.hh>
#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <memory>
#include <optional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief What a Cumulative's presence argument for one task comes to: what
     * its activity flags are reified on, and whether it has any at all.
     *
     * \sa cumulative_task_presence
     *
     * \ingroup Innards
     */
    struct CumulativeTaskPresence
    {
        /// The {0, 1} variable the task's active flag carries as a third
        /// conjunct, or nullopt when the task is unconditionally present and
        /// the flag is the two-way AND.
        std::optional<IntegerVariableID> literal;

        /// Whether the task was posted as constantly absent, in which case
        /// Cumulative leaves it out of the constraint altogether: it has no
        /// flags, no terms in any capacity row, and nothing may cite it.
        bool never_present = false;
    };

    /**
     * \brief How a Cumulative resolves the presence argument it was posted
     * with for one task, given that argument (nullopt for a constraint posted
     * without presences at all).
     *
     * Only a *constant* argument resolves away: a variable presence keeps its
     * conjunct even when its domain is already a singleton, because the
     * encoding has to say what it means without appealing to a domain the OPB
     * does not record.
     *
     * Shared, and deliberately so. A derived Cumulative pins its donor's
     * activity flags, so it has to reach exactly the same verdict about which
     * of them carry a presence literal as the donor did when it built them; a
     * second copy of this rule would be one edit away from disagreeing, and the
     * disagreement would show up as a rejected proof a long way from here.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto cumulative_task_presence(const std::optional<IntegerVariableID> & posted) -> CumulativeTaskPresence;

    /**
     * \brief Everything Cumulative's propagator reads: the task data, the
     * per-time proof flags it pins, and the per-time capacity lines it builds
     * its `pol`s on.
     *
     * Hoisted out of the propagator's closure so that a *derived* Cumulative
     * (see install_derived_cumulative) can run the same algorithm over the same
     * flags with different capacity lines. Nothing here says where the flags
     * and lines came from --- a posted constraint fills them in from its own
     * define_proof_model, a derived one from its donor's --- which is exactly
     * the separation that lets the second exist without writing to the OPB.
     *
     * The proof-side members are all empty when proofs are off.
     *
     * \ingroup Innards
     */
    struct CumulativeInputs
    {
        /// The constraint whose identity inferences are attributed to.
        ConstraintID owner = CurrentlyUnnamedConstraint{};

        std::vector<IntegerVariableID> starts, lengths, heights;
        IntegerVariableID capacity = constant_variable(0_i);

        /// Sized to the task count. nullopt for a task that is unconditionally
        /// present; otherwise the {0, 1} variable saying whether it is
        /// scheduled at all, as cumulative_task_presence resolves it. A derived
        /// Cumulative fills this in from its donors', so that the reasons it
        /// gives carry the same presence literals the flags it pins were
        /// reified on.
        std::vector<std::optional<IntegerVariableID>> presence;

        /// The tasks that can raise the load profile at all: those whose length
        /// and height can both be non-zero.
        std::vector<std::size_t> active_tasks;

        /// Indexed by `t - per_task_t_lo[i]`, over the task's possible-active
        /// window. A derived Cumulative points these at its donor's flags, so
        /// the windows must be the donor's too.
        std::vector<std::vector<ProofFlag>> before_flags, after_flags, active_flags;
        /// Per (variable-height task, t, bit), the linearised load
        /// contribution. Empty for a constant height, and empty throughout for
        /// a derived Cumulative, which takes constant heights only.
        std::vector<std::vector<std::vector<ProofFlag>>> contrib_flags;
        std::vector<Integer> per_task_t_lo;

        /// Per task, the `end >= start + length` line for the proof-only end
        /// proxy a task whose start and length both vary is pinned through, and
        /// nullopt for every other task. Shared, because a posted Cumulative's
        /// install initialiser derives it after these inputs are built; a
        /// derived Cumulative fills in its own, from what each donor published
        /// under ConstraintProofModelData<Cumulative>::end_lower_bound_role.
        std::shared_ptr<std::vector<std::optional<ProofLine>>> end_ge_lines;

        /// t -> the row saying the load at t is within the capacity. A posted
        /// constraint's are OPB rows; a derived constraint's are derived from
        /// its donor's, in the proof.
        std::map<Integer, ProofLine> capacity_lines;

        CumulativeRules rules;
        CumulativeProofMutation proof_mutation;
        CumulativePresenceMutation presence_mutation;

        /// Overload checking, resolved once (see
        /// Cumulative::prepare_overload_check). Empty when the rule is off or
        /// no task is eligible.
        std::vector<std::size_t> overload_tasks;
        std::vector<Integer> time_slot_prefix;
        Integer time_slot_lo = 0_i;
    };

    /**
     * \brief The time points one of a Cumulative's tasks could possibly be
     * active at, inclusive at both ends.
     *
     * \sa cumulative_task_window
     *
     * \ingroup Innards
     */
    struct CumulativeTaskWindow
    {
        Integer lo, hi;
    };

    /**
     * \brief Where a task's per-time flags run from and to: `[lb(start),
     * ub(start) + ub(length) - 1]`.
     *
     * A task can be active from its earliest start to its latest finish, so the
     * window takes the *largest* duration still allowed --- which for a variable
     * length means its upper bound, not the number it will turn out to be.
     *
     * Shared rather than written out per caller because every caller has to
     * agree with the donor, and the failure mode when one does not is silence:
     * install_derived_cumulative looks a donor's flags up by `(position, t)` and
     * declines when they are not there, so a window that disagrees by one costs
     * a presolver its inference without anything saying so.
     *
     * `initial_state` because these are resolved once, before the search: the
     * flags exist over this window for the whole of it, whatever the bounds do
     * later.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto cumulative_task_window(const State & initial_state, const IntegerVariableID & start, const IntegerVariableID & length)
        -> CumulativeTaskWindow;

    /**
     * \brief What the overload check needs resolving once, before the search
     * starts: which tasks its window-energy lemma can speak about, and where a
     * capacity row exists to be cited.
     *
     * \ingroup Innards
     */
    struct CumulativeOverloadData
    {
        std::vector<std::size_t> overload_tasks;
        std::vector<Integer> time_slot_prefix;
        Integer time_slot_lo = 0_i;
    };

    /**
     * \brief Resolve CumulativeOverloadData from a constraint's posted
     * arguments and the initial state.
     *
     * Shared by a posted Cumulative and a derived one, so that a derived
     * constraint gets the same energy reasoning over its donor's flags rather
     * than a second implementation of the eligibility rules.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto prepare_cumulative_overload_check(const std::vector<IntegerVariableID> & starts,
        const std::vector<IntegerVariableID> & lengths, const std::vector<IntegerVariableID> & heights, const std::vector<std::size_t> & active_tasks,
        const std::vector<Integer> & per_task_t_lo, const std::vector<Integer> & per_task_t_hi, const State & initial_state)
        -> CumulativeOverloadData;

    /**
     * \brief Time-table propagation and overload checking for Cumulative.
     *
     * Instantiated for both inference trackers; see the bottom of
     * cumulative.cc.
     *
     * \ingroup Innards
     */
    auto propagate_cumulative(const CumulativeInputs &, const State &, auto & inference_tracker, ProofLogger * const logger) -> PropagatorState;
}

#endif
