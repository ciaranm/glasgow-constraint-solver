#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_PROPAGATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_PROPAGATE_HH

#include <gcs/constraint_id.hh>
#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/constraints/innards/task_presence.hh>
#include <gcs/constraints/innards/window_energy.hh>
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
#include <tuple>
#include <vector>

namespace gcs::innards
{
    struct CheckpointRecoveryCache;

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
        /// scheduled at all, as task_presence resolves it. A derived
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
        /// Where each task's flags run from and to, inclusive. The `hi` half
        /// is what edge-finding needs: a window can extend past the last time a
        /// task could be active, and both the rule and its certificate have to
        /// clip to the same place or the propagator will fire where the lemma
        /// cannot derive what it assumed.
        std::vector<Integer> per_task_t_lo, per_task_t_hi;

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

        /// Where an inference gets the row for a time point from, when it is
        /// not \ref capacity_lines: recovered from the start-checkpoint block,
        /// in the proof, and cached. Null unless
        /// CumulativeEncoding::BothRecovering asked for it --- and shared with
        /// the initialiser that checks each recovery against the model row, so
        /// that an inference cites the same line the check passed on rather
        /// than deriving its own copy.
        ///
        /// Set and non-null does not mean every row comes from here: a
        /// Cumulative the recovery cannot speak about (a variable height, an
        /// optional task) falls back to \ref capacity_lines, which is why the
        /// two live side by side rather than one replacing the other.
        std::shared_ptr<CheckpointRecoveryCache> checkpoint_recovery;

        /// #780: whether a variable-height task's *pair* contribution bits are
        /// defined as conjunctions with the height's own bits (two reification
        /// halves each) rather than linearised by three rows per pair. False
        /// only where some height has no citable bits --- a view, or a declared
        /// lower bound below zero --- and then the recovery declines any
        /// constraint with a variable height, because the swap it does is
        /// stated over those halves.
        bool pair_contribution_bits_are_conjunctions = false;

        CumulativeRules rules;
        CumulativeProofMutation proof_mutation;
        CumulativePresenceMutation presence_mutation;

        /// Overload checking, resolved once (see
        /// Cumulative::prepare_overload_check). Empty when the rule is off or
        /// no task is eligible.
        std::vector<std::size_t> overload_tasks;
        std::vector<Integer> time_slot_prefix;
        Integer time_slot_lo = 0_i;

        /// Edge-finding's window-energy rows, keyed on (task, window lo, window
        /// hi, low guard, high guard, the length the task was counted at). They
        /// are facts about the model rather than about the
        /// search state, so they live at ProofLevel::Top and every later firing
        /// over the same window cites the same line. Shared, and mutable
        /// through the shared_ptr, because the propagator closure holds these
        /// inputs by value and const.
        ///
        /// Worth having by a wide margin: measured over the Pack instances, a
        /// row is cited between 322 and 3455 times for each time it is derived,
        /// because a window is a pair of an earliest start and a latest
        /// completion time and those repeat constantly. Re-deriving per firing
        /// costs about a hundred times more.
        std::shared_ptr<std::map<std::tuple<std::size_t, Integer, Integer, Integer, Integer, Integer>, window_energy::GuardedWindowEnergy>>
            guarded_energy;
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
