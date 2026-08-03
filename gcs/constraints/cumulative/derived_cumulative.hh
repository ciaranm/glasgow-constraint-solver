#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_DERIVED_CUMULATIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_DERIVED_CUMULATIVE_HH

#include <gcs/constraint_id.hh>
#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <functional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief A Cumulative whose proof semantics are *derived* rather than
     * asserted: it adds no rows to the OPB, and establishes its per-time
     * capacity rows inside the proof instead, from a donor Cumulative's.
     *
     * This is what lets a presolver add an implied Cumulative without touching
     * the model. The model is the statement being verified, so a presolver that
     * wrote its inference into the OPB would be changing that statement rather
     * than proving anything about it --- VeriPB would verify the result and it
     * would mean nothing.
     *
     * The derived constraint covers the donor's tasks, with its own heights and
     * capacity. It creates no flags: it pins the donor's, found through the keys
     * ConstraintProofModelData<Cumulative> publishes, which is also what checks
     * that the two agree about the tasks' possible-active windows --- a key
     * outside the window the donor encoded has no flag, and this declines rather
     * than inventing one.
     *
     * \ingroup Innards
     */
    struct DerivedCumulativeSpec
    {
        /// The Cumulative whose flags and capacity rows this is derived from.
        /// Its arguments come from the donor's own accessors. The donor must
        /// not be an optional-task Cumulative: its active flags would carry a
        /// presence conjunct, and a derived constraint reasoning over them
        /// would need the donor's presence literals in every reason it gives.
        /// A caller building one of these from a donor should decline when the
        /// donor's presences() is non-empty.
        ConstraintID donor;

        /// The donor's starts, in the donor's order: the flag keys are by task
        /// position, so these must be the donor's tasks and nothing else.
        std::vector<IntegerVariableID> starts;

        /// Constant by type, which is the v1 restriction made structural: a
        /// variable height enters the donor's capacity row as a bit-linearised
        /// contribution rather than as `height x active`, and the derived row
        /// would have to speak about those bits too.
        std::vector<Integer> lengths, heights;
        Integer capacity;

        /**
         * \brief How the derived row for time `t` comes off the donor's.
         *
         * Called once per time point, at ProofLevel::Top, with the donor's row
         * for `t`; returns the derived row, which must say
         * `Σ heights[i]·active[i,t] ≤ capacity` over the donor's flags. Anything
         * else and the propagator's `pol`s will not cancel, which VeriPB will
         * say so about.
         *
         * A recipe is a derivation, never an axiom: it has a ProofLogger and no
         * ProofModel, so it cannot write to the OPB even by mistake.
         */
        std::function<auto(ProofLogger &, ProofLine donor_row, Integer t)->ProofLine> recipe;

        /// Which propagation rules the derived constraint runs. The default is
        /// all of them: it gets the same time-tabling and overload checking a
        /// posted Cumulative does, over the donor's flags.
        CumulativeRules rules;
    };

    /**
     * \brief Install a derived Cumulative's propagator.
     *
     * For a presolver to call, in the shape auto_table and the difference-logic
     * presolver already use: there is no constraint to post, because posting is
     * what writes to the OPB.
     *
     * Returns false when the derived constraint could not be set up --- proofs
     * are on but the donor's flags or rows are not where its published keys say,
     * which means the donor was never installed, or the windows disagree. That
     * is a decline, not a failure: the caller should not install a propagator
     * whose inferences it cannot justify. With proofs off there is nothing to
     * cite and nothing to decline, and the propagator installs unconditionally,
     * so the same inferences are drawn either way.
     *
     * \ingroup Innards
     */
    auto install_derived_cumulative(Propagators &, const State & initial_state, ProofLogger * const, DerivedCumulativeSpec) -> bool;
}

#endif
