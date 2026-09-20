#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_PARITY_SYSTEM_GATHERING_PARITY_SYSTEM_GATHERING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_PARITY_SYSTEM_GATHERING_PARITY_SYSTEM_GATHERING_HH

#include <gcs/presolver.hh>
#include <gcs/stats.hh>

#include <cstddef>
#include <memory>
#include <string>
#include <vector>

namespace gcs
{
    /**
     * \brief What the parity-system gathering presolver did, filled in when it
     * runs.
     *
     * As for DifferenceLogicStats, these counts are not decoration: they are the
     * only thing that tells "gathered the system" from "silently gathered
     * nothing". A presolver that lifted no rows --- because, say, ParityOdd
     * stopped publishing its chain naming, so find_parity_chain started
     * returning nullopt for every donor --- adds no OPB content, changes no
     * solution, and leaves every proof verifying. It would pass every
     * solution-equivalence check, OPB byte-diff and VeriPB run there is, and
     * look exactly like a model with no XOR structure in it.
     *
     * Being a ComponentStats is what puts these into a report without anything
     * having to list them: `fzn-glasgow` renders every registered block through
     * entries().
     *
     * \sa ParitySystemGathering
     * \ingroup Presolvers
     */
    struct ParitySystemGatheringStats final : ComponentStats
    {
        /// Donor rows lifted into a system that got a propagator: the number
        /// that matters.
        std::size_t rows_gathered = 0;

        /// Distinct atoms those rows span, after canonicalisation --- so after
        /// `v != c` and `v == c` have been recognised as one column, and after
        /// duplicates within a row have cancelled.
        std::size_t atoms = 0;

        /// Propagators installed: one per connected component of the rows that
        /// were gathered, since rows sharing no atom cannot inform each other
        /// and eliminating over them together is pure waste.
        std::size_t components_installed = 0;

        /// Donor propagators retired, because the system subsumes them.
        std::size_t donor_propagators_disabled = 0;

        /**
         * \brief How many rows were offered by a Boolean `Equals` / `NotEquals`
         * donor rather than by a ParityOdd.
         *
         * Offered, not gathered: such a row still has to land in a component
         * with something else, and rows_gathered is what counts those. Broken
         * out because it is a separate detection path over a separate class
         * hierarchy, and the one that can regress silently on its own --- a
         * model whose XORs were all posted as ParityOdd would still look busy.
         */
        std::size_t boolean_rows_offered = 0;

        /**
         * \name Why a candidate was not gathered.
         *
         * Every ParityOdd and every ReifiedEquals in the model falls into
         * exactly one of rows_gathered, skipped_alone_in_component, or one of
         * these, so the counts together account for all of them.
         * @{
         */

        /// A ParityOdd over no literals. It asserts that zero is odd, and its
        /// own propagator refutes it at the root; lifting it would be this
        /// presolver claiming a refutation that was never its business, and
        /// there is nothing for elimination to do with a row that has no atoms.
        std::size_t skipped_empty_row = 0;

        /// A donor whose accumulator chain could not be recovered in full: it
        /// published no naming, or published one and some row under it was never
        /// emitted. The justifications are `pol`s over rows derived from that
        /// chain, so a chain that is not all there is not a weaker proof but an
        /// invalid one. Only ever non-zero when proofs are being logged: with no
        /// logger there is nothing to cite and nothing to check.
        std::size_t skipped_uncitable_chain = 0;

        /// A Boolean donor whose reification condition is neither
        /// reif::MustHold nor reif::MustNotHold. A conditional equality is not a
        /// parity row at all until its condition is decided, and the system has
        /// no vocabulary for a row that might not be there. A deliberate gap
        /// rather than an impossibility --- #649's equivalence store is where it
        /// would be picked up --- and counted rather than guessed at.
        std::size_t skipped_reified = 0;

        /// A Boolean donor with an operand whose declared domain reaches outside
        /// `{0, 1}`. Over wider operands equality is not a parity constraint at
        /// all: `x = y` says far more than "the same number of them are
        /// non-zero", so lifting it would be unsound rather than merely weak.
        std::size_t skipped_wide_operands = 0;

        /// A row that ended up alone in its component, once atoms had been
        /// shared out. Over a single row the system propagator computes exactly
        /// what that row's own ParityOdd computes, more slowly, so it is left to
        /// it --- and its propagator is not retired. This is also where a row
        /// whose atoms all cancelled goes (`ParityOdd({x, x})`), since a row
        /// with no atoms can share none.
        std::size_t skipped_alone_in_component = 0;

        ///@}

        [[nodiscard]] auto component_name() const -> std::string override;
        [[nodiscard]] auto summary() const -> std::string override;
        [[nodiscard]] auto entries() const -> std::vector<StatsEntry> override;
    };

    /**
     * \brief Scan a posted Problem for XOR-shaped constraints, gather them into
     * GF(2) systems, and install a Gauss-Jordan propagator over each.
     *
     * A model does not have to be rewritten against ParitySystem to get
     * system-level parity reasoning: post the XORs as ordinary ParityOdd
     * constraints, add this presolver, and each connected component of them is
     * eliminated over as one system. That is how a model arriving through a
     * frontend gets here, since XOR structure survives MiniZinc flattening as
     * individual `array_bool_xor` constraints and there is nothing to re-model.
     *
     * A single ParityOdd is already GAC on its own row --- unit propagation on
     * one parity constraint *is* GAC --- so everything this buys lives in the
     * conjunction. See dev_docs/parity-system.md.
     *
     * \par What is gathered
     *
     * Two donor families. A ParityOdd is a row directly. A Boolean `Equals` or
     * `NotEquals` --- both operands' declared domains within `{0, 1}` --- is a
     * 2-XOR: `x != y` is `[x != 0] XOR [y != 0] = 1`, and `x = y` is the same
     * with one literal negated, since `!p` is `p XOR 1`. The second family is
     * where a MiniZinc model's `bool_eq` and `bool_not` rows come from, and it is
     * worth having less for the rows themselves than for the atoms they share:
     * they are the edges that join what would otherwise be separate components.
     * Everything else is skipped and counted --- see
     * ParitySystemGatheringStats.
     *
     * Off by default, as every presolver is: opted into with
     * Problem::add_presolver.
     *
     * \par Why this can be a presolver at all
     *
     * Presolvers run after create_propagators and after the proof model has been
     * finalised, so no new OPB content can be added --- Presolver::run has no
     * ProofModel * precisely because that door has closed. The slack-form rows
     * the justifications need are therefore derived *inside* the proof, at
     * ProofLevel::Top, from rows each donor already emitted. That is not a
     * limitation worked around; it is the chain-portable option anyway, since a
     * row only our own `.opb` contained would fail against the one cake_pb_cp
     * re-derives from the `.scp`.
     *
     * \ingroup Presolvers
     */
    class ParitySystemGathering : public Presolver
    {
    private:
        std::shared_ptr<ParitySystemGatheringStats> _stats;
        bool _keep_donor_propagators;

    public:
        /**
         * \brief Construct the presolver, optionally sharing a stats block that
         * will be filled in when it runs.
         *
         * The block is shared, not copied, so it survives
         * Problem::add_presolver cloning the presolver and can be read after
         * solving.
         */
        explicit ParitySystemGathering(std::shared_ptr<ParitySystemGatheringStats> stats = nullptr);

        /**
         * \brief Leave the gathered donors' own propagators running, instead of
         * retiring them.
         *
         * Ships **off**, unlike DifferenceLogic's equivalent: the system
         * propagator subsumes a single XOR's unit propagation outright (a donor
         * row with one literal left becomes a unit row of the reduced system, so
         * the system infers exactly what the donor would have), and a donor
         * whose rows have been gathered is then pure overhead on every wake.
         *
         * This exists so that the subsumption claim can be checked rather than
         * assumed, and it is a strong check: disabling a propagator changes
         * neither degrees nor adjacency, so the search tree must come out
         * **node for node identical** either way. It differing means the
         * subsumption claim is wrong.
         *
         * Donors in a component that got no propagator are never retired,
         * however this is set.
         */
        auto keeping_donor_propagators(bool = true) -> ParitySystemGathering &;

        [[nodiscard]] virtual auto run(Problem &, innards::Propagators &, innards::State &, innards::ProofLogger * const) -> bool override;
        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Presolver> override;
    };
}

#endif
