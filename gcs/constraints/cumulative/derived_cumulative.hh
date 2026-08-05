#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_DERIVED_CUMULATIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_DERIVED_CUMULATIVE_HH

#include <gcs/constraint_id.hh>
#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/constraints/innards/makespan_energy.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <functional>
#include <map>
#include <optional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief One task of a derived Cumulative, and where its activity flags are
     * to be found.
     *
     * A derived constraint creates no flags of its own, so every task has to
     * point at a posted Cumulative that already encoded it: `donor` says which,
     * and `position` says which of that donor's tasks it is, since the flag keys
     * ConstraintProofModelData publishes are by task position.
     *
     * Tasks may name *different* donors. That is what an inferred constraint
     * over several resources needs --- a clique whose members conflict pairwise
     * on different resources has no single donor covering all of it --- and it
     * is the caller's job to make sure the flags it points at mean the same
     * thing as the ones its rows are derived from, which
     * recover_conjunction_flag_bridge exists to establish.
     *
     * \ingroup Innards
     */
    struct DerivedCumulativeTask
    {
        /// The posted Cumulative whose flags express this task's activity.
        ConstraintID donor;

        /// This task's index within that donor's own task list.
        std::size_t position;

        /// The start variable, which must be the one the donor was posted with
        /// at `position`: the flags are reified on it, so a different variable
        /// would silently mean something else.
        IntegerVariableID start;

        /// Constant by type, which is the v1 restriction made structural: a
        /// variable height enters a donor's capacity row as a bit-linearised
        /// contribution rather than as `height x active`, and a derived row
        /// would have to speak about those bits too.
        Integer length, height;
    };

    /**
     * \brief The donors' capacity rows for one time point, by donor, as handed
     * to a recipe.
     *
     * Only donors that wrote a row for that time point appear: a donor whose own
     * tasks cannot be active then has nothing there to cite, which is a fact
     * about the donor and not an error.
     *
     * \ingroup Innards
     */
    using DerivedCumulativeRows = std::map<ConstraintID, ProofLine>;

    /**
     * \brief A Cumulative whose proof semantics are *derived* rather than
     * asserted: it adds no rows to the OPB, and establishes its per-time
     * capacity rows inside the proof instead, from posted Cumulatives'.
     *
     * This is what lets a presolver add an implied Cumulative without touching
     * the model. The model is the statement being verified, so a presolver that
     * wrote its inference into the OPB would be changing that statement rather
     * than proving anything about it --- VeriPB would verify the result and it
     * would mean nothing.
     *
     * \ingroup Innards
     */
    struct DerivedCumulativeSpec
    {
        /// The derived constraint's tasks, each pointing at the donor that
        /// encoded it. No donor may be an optional-task Cumulative: its active
        /// flags would carry a presence conjunct, and a derived constraint
        /// reasoning over them would need that donor's presence literals in
        /// every reason it gives. A caller building one of these should decline
        /// when a donor's presences() is non-empty.
        std::vector<DerivedCumulativeTask> tasks;

        Integer capacity;

        /// The donors whose per-time capacity rows the recipe wants to build
        /// on. Usually the same donors the tasks name, but not necessarily ---
        /// a pairwise conflict is witnessed by whichever resource cannot hold
        /// both tasks, which need not be where either task's flags are taken
        /// from.
        std::vector<ConstraintID> row_donors;

        /**
         * \brief How the derived row for time `t` is established.
         *
         * Called once per time point, at ProofLevel::Top, with the rows those
         * of \ref row_donors that have one wrote for `t`; returns the derived
         * row, which must say `Σ heights[i]·active[i,t] ≤ capacity` over the
         * flags \ref tasks point at. Anything else and the propagator's `pol`s
         * will not cancel, which VeriPB will say so about.
         *
         * Returning nullopt means this time point cannot be derived, and the
         * whole constraint is then declined: a derived Cumulative needs a row
         * everywhere its propagator will cite one, so there is no useful
         * halfway house.
         *
         * A recipe is a derivation, never an axiom: it has a ProofLogger and no
         * ProofModel, so it cannot write to the OPB even by mistake.
         */
        std::function<auto(ProofLogger &, const DerivedCumulativeRows &, Integer t)->std::optional<ProofLine>> recipe;

        /**
         * \brief A variable every task must finish by, if there is one: the
         * makespan this constraint's energy bounds from below.
         *
         * Set it, along with \ref makespan_links, and the constraint pushes that
         * variable's lower bound once, at the root, with a certificate. What
         * makes the variable a makespan is those links: the rows saying each
         * task finishes by it are what confine the tasks to the window the
         * argument counts supply over, and they are summed into the derivation
         * rather than taken on trust. Name a variable that is not a makespan
         * and the bound is simply weaker, not wrong.
         *
         * The bound is found from the task geometry and the links' bounds
         * alone, so it is the same with proofs off; only the certificate needs
         * a logger.
         */
        std::optional<IntegerVariableID> makespan = std::nullopt;

        /// Per task, the model row saying that task must finish by the
        /// makespan. A task with none keeps only what its own domain gives,
        /// which is a weaker bound rather than a wrong one; see
        /// find_makespan_links, which is what a presolver builds this with.
        std::vector<std::optional<makespan_energy::MakespanLink>> makespan_links = {};

        /// Called with the bound, if one is reached. For a presolver to record
        /// what its inference came to, which is the number a bounds artefact
        /// reports.
        std::function<auto(Integer)->void> makespan_bound_reached = {};

        /// Corrupt the makespan bound's certificate. For tests only, which
        /// assert that VeriPB rejects the result; see MakespanEnergyMutation.
        makespan_energy::MakespanEnergyMutation makespan_mutation = makespan_energy::makespan_energy_mutation::None{};

        /// Which propagation rules the derived constraint runs. The default is
        /// all of them: it gets the same time-tabling and overload checking a
        /// posted Cumulative does, over the donors' flags.
        CumulativeRules rules;
    };

    /**
     * \brief Build the task list for the common case of a derived Cumulative
     * over all of one donor's tasks, in the donor's order.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derived_cumulative_tasks_from(const ConstraintID & donor, const std::vector<IntegerVariableID> & starts,
        const std::vector<Integer> & lengths, const std::vector<Integer> & heights) -> std::vector<DerivedCumulativeTask>;

    /**
     * \brief Install a derived Cumulative's propagator.
     *
     * For a presolver to call, in the shape auto_table and the difference-logic
     * presolver already use: there is no constraint to post, because posting is
     * what writes to the OPB.
     *
     * Returns false when the derived constraint could not be set up --- proofs
     * are on but a donor's flags are not where its published keys say, which
     * means the donor was never installed or the windows disagree, or the recipe
     * declined a time point. That is a decline, not a failure: the caller should
     * not install a propagator whose inferences it cannot justify. With proofs
     * off there is nothing to cite and nothing to decline, and the propagator
     * installs unconditionally, so the same inferences are drawn either way.
     *
     * \ingroup Innards
     */
    auto install_derived_cumulative(Propagators &, const State & initial_state, ProofLogger * const, DerivedCumulativeSpec) -> bool;
}

#endif
