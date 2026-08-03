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
#include <utility>
#include <vector>

namespace gcs::innards
{
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
        /// scheduled at all. A derived Cumulative fills this with nullopts:
        /// deriving over an optional donor would need the presence literals in
        /// its own reasons, which is future work (see DerivedCumulativeSpec).
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

        /// The proof-only `end = start + length` proxy for a task whose start
        /// and length both vary, and the `{end >= s + l, end <= s + l}` lines
        /// its initialiser cached. Shared, so the cache survives across calls.
        std::vector<std::optional<ProofOnlySimpleIntegerVariableID>> ends;
        std::shared_ptr<std::vector<std::optional<std::pair<ProofLine, ProofLine>>>> end_lines;

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
