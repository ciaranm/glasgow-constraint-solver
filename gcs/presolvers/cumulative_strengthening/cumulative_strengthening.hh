#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_CUMULATIVE_STRENGTHENING_CUMULATIVE_STRENGTHENING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_CUMULATIVE_STRENGTHENING_CUMULATIVE_STRENGTHENING_HH

#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/constraints/cumulative/derived_cumulative_stats.hh>
#include <gcs/integer.hh>
#include <gcs/presolver.hh>
#include <gcs/presolvers/innards/cumulative_strengthening_mutations.hh>
#include <gcs/stats.hh>

#include <cstddef>
#include <memory>
#include <string>
#include <variant>
#include <vector>

namespace gcs
{
    /**
     * \brief What the Cumulative strengthening presolver did, filled in when it
     * runs.
     *
     * The presolver is invisible from the outside by construction: it writes
     * nothing to the OPB, removes no solution, and --- because the rules it
     * applies are time-table neutral --- does not even change the search tree
     * unless energy reasoning is switched on. So every check that a presolver
     * normally has to pass is passed just as well by a presolver that did
     * nothing at all, and the counts below are how a test tells the two apart.
     *
     * The presolver allocates one of these whether or not a caller asked for
     * one, so the block reaches Stats::components() and says what happened even
     * when nobody was interested enough to pass a handle in --- which is the
     * configuration in which "the presolver quietly stopped firing" used to be
     * unobservable.
     * \sa CumulativeStrengthening
     *
     * \ingroup Presolvers
     */
    struct CumulativeStrengtheningStats final : ComponentStats
    {
        /// Posted Cumulatives the presolver looked at.
        std::size_t donors_seen = 0;

        /// Donors it posted a strengthened, derived Cumulative for: the number
        /// that matters.
        std::size_t donors_strengthened = 0;

        /// Summed `capacity - kappa` over those donors. Distinguishes "fired on
        /// three constraints" from "fired on three constraints and took a unit
        /// off each", which are different claims about the fixture.
        Integer capacity_units_removed = 0_i;

        /// Donors that were strengthened over only part of themselves, because
        /// a task could not be argued about at all: a height that is a view,
        /// whose reification is over its own bit vector, or one whose lower
        /// bound is zero and so guarantees nothing. Its terms are weakened away
        /// and it takes no part; what that costs is a weaker strengthening,
        /// never a wrong one. Counted because a donor drifting into this looks
        /// exactly like one that was strengthened in full. Neither a variable
        /// *length* nor an ordinary variable height is one of these any more.
        std::size_t donors_with_set_aside_tasks = 0;

        /// Donors where converting a variable-height task into its guaranteed
        /// demand would have made the strengthening *worse*, so it was set
        /// aside after all. Adding a task can only push the largest subset sum
        /// up, so a conversion can cost a donor the very reduction this
        /// presolver exists to make; both are worked out and the bigger
        /// reduction kept. Counted because the two look identical from outside
        /// and this is the only thing that says the choice was made.
        std::size_t donors_better_off_setting_heights_aside = 0;

        /// Tasks kept by converting a variable height into its lower bound ---
        /// the demand the task is guaranteed to make --- rather than setting
        /// them aside, summed over the donors that kept them.
        std::size_t converted_heights = 0;

        /// Tasks whose height was raised to the strengthened capacity, over
        /// those donors: the other half of what the presolver does, and the
        /// only record that it happened, since a raise can leave the capacity
        /// untouched and a capacity reduction can raise nothing.
        std::size_t tasks_raised = 0;

        /**
         * \name Why a donor was passed over.
         *
         * Broken out because they mean different things to a caller: an
         * argument this presolver cannot reduce, a proof-size budget a caller
         * may want to raise, the honest and common answer that there was
         * nothing to say, and a bug.
         *
         * What is *not* among them is anything about a task. A variable
         * height, a variable length and an optional task each cost at most the
         * task itself --- its term is weakened out, or converted, and the donor
         * keeps its strengthening. The capacity is the one argument still able
         * to turn a whole donor away.
         */
        ///@{
        /// Donors whose capacity could not be reduced to a number to argue
        /// against, which today means a view capacity: its reification is over
        /// its own bit vector, so the bound rows do not cancel against the
        /// row's. Named for the condition rather than for today's only instance
        /// of it --- see cumulative_donor_view.
        std::size_t declined_irreducible_capacity = 0;
        /// Donors with a *mandatory* task whose guaranteed demand exceeds the
        /// capacity, so the donor is infeasible on its own and its own
        /// propagator will say so. Not a decline this presolver should be
        /// pleased about, and so not counted with the ones it should --- a
        /// fixture that accidentally builds an infeasible donor would otherwise
        /// read as a correct "nothing to gain". An *optional* task of that
        /// shape says only that its presence is false, and cumulative_donor_view
        /// sets it aside instead, so the rest of the donor is still
        /// strengthened.
        std::size_t declined_infeasible_donor = 0;
        /// Donors whose capacity is too large to subset-sum over. Unlike the
        /// two below it this one is not about proof size: the assessment itself
        /// is a bitset of `capacity` bits rebuilt at every time point, so it
        /// costs whether or not proofs are on, and the cost is the capacity's
        /// magnitude rather than anything the model says about the tasks.
        std::size_t declined_capacity_too_large = 0;
        std::size_t declined_over_budget = 0;
        std::size_t declined_over_raise_budget = 0;
        /// The capacity was already the largest load the tasks can reach, and
        /// no height moved either, so there was nothing to strengthen.
        std::size_t declined_nothing_to_gain = 0;
        ///@}

        /**
         * \name Which derivation each per-time capacity row took.
         *
         * Zero when proofs are off, since there are no rows to derive. The
         * split is the difference between Schulz's gcd rule and his knapsack
         * rule as they reach the proof --- see CumulativeStrengthening --- and
         * a fixture that means to exercise one of them has to assert which it
         * got, because the arithmetic picks whichever is stronger and a fixture
         * can drift onto the other path without failing anything else.
         */
        ///@{
        std::size_t rows_by_division = 0;
        std::size_t rows_by_dynamic_programming = 0;
        ///@}

        /**
         * \name What the raising cost, in the proof.
         *
         * Zero when proofs are off. `rows_with_a_raise` counts time points at
         * which some task's height was raised, whatever that took --- including
         * the degenerate case where a raised task is the only one that can run
         * then, and the row is a bare `active <= 1` with no at-most-one behind
         * it. `raise_lines_emitted` counts the steps that took, which is not
         * one per raised task --- how
         * many a raise takes depends on how far the rest of the row overshoots
         * the capacity, and is the sequence
         * CumulativeStrengthening::with_raise_budget caps. It does not count
         * the at-most-ones themselves, nor the implication steps that relax a
         * row's right hand side, both of which are bounded by the tasks
         * present rather than by the arithmetic.
         */
        ///@{
        std::size_t rows_with_a_raise = 0;
        std::size_t raise_lines_emitted = 0;
        ///@}

        /// What installing the strengthened constraints came to, summed over
        /// every donor: one derived Cumulative is installed per strengthened
        /// donor, and one component entry per derived constraint would be noise
        /// where this is what a reader wants.
        DerivedCumulativeStats derived;

        [[nodiscard]] virtual auto component_name() const -> std::string override;
        [[nodiscard]] virtual auto summary() const -> std::string override;
        [[nodiscard]] virtual auto entries() const -> std::vector<StatsEntry> override;
    };

    /**
     * \brief Strengthen each posted Cumulative by integrality, posting the
     * strengthened version as a *derived* constraint whose per-time capacity
     * rows are proved from the donor's.
     *
     * The rules are Schulz's pre-solving strengthenings, as recapped by
     * Cloutier and Quimper (CP 2026, section 2.3). The load at a time point is a
     * sum of the heights of the tasks running then, so it can only ever take a
     * value that is a subset sum of those heights; a capacity that is not itself
     * such a value is therefore worth more than it says. Reducing it to
     *
     *     kappa = max over t of (largest subset sum of the heights of the tasks
     *                            that can run at t, that is at most the capacity)
     *
     * loses no solution --- as long as the tasks that quantity is a subset sum
     * *of* are the right ones. Schulz's two capacity rules are the two ways it
     * gets computed --- his gcd rule is the case where the heights share a
     * factor `d`, making the answer `d * floor(C / d)`, and his knapsack rule
     * is the general one --- and they reach the proof as the two derivations
     * derive_subset_sum_strengthening() chooses between: two `pol` steps of
     * Chvatal-Gomory rounding, or a layered dynamic program. Which one a row
     * took is in CumulativeStrengtheningStats.
     *
     * The right tasks are the ones that can run beside something. A task that
     * cannot --- `c_i + c_j > C` for every other `j` that consumes anything and
     * whose window overlaps its own --- occupies the resource whenever it runs,
     * so it reaches `C` on its own and would make kappa the capacity and the
     * rule do nothing. Set those aside and kappa is computed over the rest;
     * their own heights then come down to kappa, which is what makes setting
     * them aside sound and is Schulz's coefficient-raising rule arriving at the
     * same place from the other direction. Both of his height rules are
     * therefore this one step, and it is what
     * CumulativeStrengtheningStats::tasks_raised counts.
     *
     * That step is where the proof gets expensive. A raised task's row has to
     * be built out of at-most-ones taken off the donor's own row --- one per
     * pair --- and then the task's coefficient walked up to kappa a `pol` at a
     * time, because cutting planes cannot raise a coefficient to the right hand
     * side in one division unless the rest of the row barely overshoots it. See
     * with_raise_budget(), and `dev_docs/cumulative-strengthening.md` for the
     * arithmetic.
     *
     * **Do not expect this to make anything faster on its own.** The rules are
     * time-table neutral --- a load is a sum of heights, so it clears `C`
     * exactly when it clears kappa --- which the paper says outright and which
     * the tests assert as a tripwire, since a search-tree difference under
     * time-tabling alone would mean the strengthening was unsound. The benefit
     * arrives with energy reasoning, where a window's supply is the capacity
     * times its width and that is not a sum of heights.
     *
     * \ingroup Presolvers
     */
    class CumulativeStrengthening : public Presolver
    {
    private:
        std::shared_ptr<CumulativeStrengtheningStats> _stats;
        long long _max_dynamic_programming_states;
        long long _max_raise_lines;
        long long _max_subset_sum_capacity;
        CumulativeRules _rules;
        innards::CumulativeStrengtheningMutation _mutation;

    public:
        /**
         * \brief Construct the presolver, optionally sharing a stats block that
         * outlives the copy Problem takes.
         *
         * A caller that passes none still gets one: the block is allocated
         * here, registered with the search's Stats when run() starts, and
         * reported like any other. Silence used to be what a caller got for not
         * asking, and silence is what #662 is about.
         */
        explicit CumulativeStrengthening(std::shared_ptr<CumulativeStrengtheningStats> stats = nullptr);

        /**
         * \brief Cap the size of the dynamic-programming derivation, summed over
         * a donor's time points, in states.
         *
         * The layered dynamic program costs three flags per state and a handful
         * of lines per transition, so a donor with a large capacity and a long
         * horizon can produce a great deal of proof for a strengthening worth
         * one unit. A donor whose derivation would exceed this is passed over
         * entirely and counted in CumulativeStrengtheningStats::declined_over_budget;
         * the divisibility path is not budgeted, being two `pol` steps a row.
         *
         * The default is meant to be left alone. It exists as a knob so that a
         * test can set it to zero and watch the dynamic-programming path
         * disappear while the divisibility one keeps working.
         */
        auto with_dynamic_programming_budget(long long states) -> CumulativeStrengthening &;

        /**
         * \brief Cap the number of proof lines spent raising heights, summed
         * over a donor's time points and raised tasks.
         *
         * A raise is a `pol` per step, and the number of steps depends on how
         * far the rest of the row overshoots the capacity: a row that only just
         * overshoots raises in one, and one that overshoots by half pays a line
         * per unit of the strengthened capacity. So the cost is not something a
         * caller can read off the model, and a donor whose raising would exceed
         * this is passed over entirely and counted in
         * CumulativeStrengtheningStats::declined_over_raise_budget.
         *
         * Separate from the dynamic-programming budget because the two buy
         * different things and are counted in different units: a donor can want
         * one and not the other, and a test setting either to zero should watch
         * only its own half disappear.
         */
        auto with_raise_budget(long long lines) -> CumulativeStrengthening &;

        /**
         * \brief Cap the capacity this presolver will subset-sum over, and so
         * decline any donor posted with a larger one.
         *
         * Not a proof budget: the two above bound what a derivation costs, and
         * this bounds what deciding whether to make one costs. `kappa` is found
         * with a word-parallel bitset over the capacity's whole range, rebuilt
         * at every time point of every donor, and that runs with proofs off
         * too. A capacity in scaled units --- a resource measured in
         * thousandths, say --- makes the assessment alone hundreds of megabytes
         * of allocation and a horizon's worth of sweeps, for a strengthening
         * nothing has yet said is worth having.
         *
         * The default is meant to be left alone; it exists as a knob so that a
         * test can set it low and watch the decline appear. A donor over it is
         * counted in CumulativeStrengtheningStats::declined_capacity_too_large.
         */
        auto with_subset_sum_capacity_limit(long long capacity) -> CumulativeStrengthening &;

        /**
         * \brief Select which propagation rules the derived constraints run.
         *
         * The default is the energy rules only, because time-tabling a derived
         * constraint is provably wasted work: neutrality says a load exceeds
         * kappa exactly when it exceeds the donor's capacity, so every
         * time-table inference the derived constraint could draw is one the
         * donor draws already, at every node. That is the same theorem the
         * tests check, used the other way round.
         *
         * Which is why a test asserting the neutrality has to turn time-tabling
         * back *on* here: with the derived constraint's time-tabling off, the
         * comparison would pass without kappa having been used for anything.
         */
        auto with_rules(CumulativeRules rules) -> CumulativeStrengthening &;

        /// Corrupt one step of the emitted derivation. For tests only, which
        /// assert that VeriPB rejects the result.
        auto with_proof_mutation(innards::CumulativeStrengtheningMutation mutation) -> CumulativeStrengthening &;

        [[nodiscard]] virtual auto run(Problem &, innards::Propagators &, innards::State &, innards::ProofLogger * const) -> bool override;
        /**
         * Create a copy of the presolver, sharing its stats block rather than
         * allocating a fresh one.
         *
         * Load-bearing, and easy to lose: Problem::add_presolver stores a
         * clone, and run() is called on *that*, so a clone that allocated its
         * own block would leave the caller's handle --- and the block anything
         * else is holding --- reading zero for ever.
         */
        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Presolver> override;
    };
}

#endif
