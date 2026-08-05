#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INFERRED_CUMULATIVE_INFERRED_CUMULATIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INFERRED_CUMULATIVE_INFERRED_CUMULATIVE_HH

#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/integer.hh>
#include <gcs/presolver.hh>

#include <cstddef>
#include <memory>
#include <optional>
#include <variant>

namespace gcs
{
    /**
     * \brief Deliberate corruptions of a lifted cut's certificate, for testing
     * only. VeriPB must reject each of them.
     *
     * The first two are the signature test of a lifted constraint: claim one
     * better than was derived and require a rejection. With small,
     * close-together integers a slack derivation can verify by coincidence ---
     * a `pol` that lands somewhere weaker than intended still lands somewhere
     * true --- and only a `+1` that is *refused* says the honest line is tight
     * to what the constraint goes on to assume of it.
     *
     * \ingroup Presolvers
     */
    namespace inferred_cumulative_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Pin one less capacity than the derivation supports.
        struct ClaimTighterCapacity
        {
        };

        /// Pin one more height for the first member than the derivation
        /// supports.
        struct ClaimTallerTask
        {
        };

        /// Build the dynamic programme against a capacity one smaller than the
        /// donor's row, so that its states claim the row rules out a member it
        /// does not. Unlike the two above, this corrupts the *derivation* rather
        /// than what is claimed of it, and is caught inside the replay rather
        /// than at the pin.
        struct ClaimTighterRow
        {
        };

        /// Claim a makespan one larger than a posted cut's energy supports.
        /// The same discipline again, against the other thing a cut is used
        /// for: `L` is the number this whole exercise reports, so a derivation
        /// with slack in it would report it while proving something weaker.
        struct ClaimHigherMakespanBound
        {
        };
    }

    using InferredCumulativeMutation = std::variant<inferred_cumulative_mutation::None, inferred_cumulative_mutation::ClaimTighterCapacity,
        inferred_cumulative_mutation::ClaimTallerTask, inferred_cumulative_mutation::ClaimTighterRow,
        inferred_cumulative_mutation::ClaimHigherMakespanBound>;

    /**
     * \brief What the inferred-Cumulative presolver did, filled in when it runs.
     *
     * A presolver that found nothing writes nothing, removes no solution and
     * leaves every proof verifying, so the counts are what a test has to assert
     * on to tell "working" from "no-op". `non_unit_cuts_posted` is the one that
     * separates this from the capacity-one stage before it: a cut with every
     * coefficient one is something InferredDisjunctive could also have found.
     *
     * \ingroup Presolvers
     */
    struct InferredCumulativeStats
    {
        /// Posted Cumulatives the presolver looked at.
        std::size_t donors_seen = 0;

        /// Tasks across all of them that could carry a cut: constant, with a
        /// positive length and height, and not on their own bigger than the
        /// resource.
        std::size_t tasks = 0;

        /// Covers enumerated by Algorithm 1 and then offered to Algorithm 2.
        std::size_t covers_considered = 0;

        /// Lifting subproblems solved. The paper's `N_calls` budget is against
        /// this, because it is the bottleneck of Algorithm 2.
        std::size_t lifting_subproblems = 0;

        /// Constraints Algorithm 2 inferred: what the published method would
        /// post, before anything is asked about proving them.
        std::size_t cuts_found = 0;

        /**
         * \brief Constraints the published method infers and we cannot derive.
         *
         * The headline number of this whole exercise: everything else here
         * measures the reproduction, and this measures the gap between it and a
         * *certified* reproduction. It is now **zero by construction**, which is
         * the point of certifying by replaying the lifting procedure's own
         * knapsack programme rather than looking for a short cutting-planes
         * route to its conclusion --- the earlier search dropped about one
         * constraint in twenty-five.
         *
         * It is still counted, and still means the same thing, because it is
         * the one number that would notice Algorithm 2 producing a constraint
         * that does not follow from the donor's row. Such a constraint is
         * dropped, not weakened and not posted.
         */
        std::size_t cuts_uncertifiable = 0;

        /// Cuts actually posted as derived Cumulatives: the number that matters.
        std::size_t cuts_posted = 0;

        /// Of those, the ones with a coefficient above one --- the inference
        /// this stage adds over the capacity-one stage before it.
        std::size_t non_unit_cuts_posted = 0;

        /**
         * \brief Time points whose row had to be derived over *fewer* than the
         * cut's members, because the rest were outside their windows there.
         *
         * The one number that says a restricted programme was ever built: the
         * row for a time point where every member is present uses the one
         * discovery already built, which is seeded rather than rebuilt. Zero
         * here means a fixture's tasks all share a window, which is what happens
         * whenever their start domains are `[0, horizon - length]` --- every
         * such task has the window `[0, horizon - 1]` whatever its length, so a
         * corpus built that way exercises none of this.
         */
        std::size_t restricted_rows_rebuilt = 0;

        /**
         * \brief The largest makespan bound over the posted cuts: Sidorov's
         * `L = ceil(sum_i d_i pi_i / pi_0)`.
         *
         * A cut says the tasks in it cannot occupy more than `pi_0` units of
         * the resource at once, and between them they need `sum_i d_i pi_i`
         * units over the whole schedule, so the schedule cannot be shorter than
         * their ratio. This is the number to compare against a published bound,
         * and the only output of this presolver that means anything without
         * running a search. Zero when nothing was posted.
         */
        Integer largest_capacity_bound{0};

        /**
         * \brief The largest makespan bound actually *derived*, over the posted
         * cuts, when a makespan variable was given.
         *
         * The certified counterpart of \ref largest_capacity_bound, and the one
         * that comes with a `.pbp`. It is usually the same number, and can be
         * larger: `L` assumes the tasks may start at time zero, while the
         * derivation argues over the window the tasks' earliest starts actually
         * leave them, and every time point before that window is a unit the
         * resource never had to supply. It can also be smaller, when a task the
         * window-energy lemma cannot speak about carries some of the energy `L`
         * counted.
         *
         * Zero when no makespan was given, or when nothing was posted.
         */
        Integer certified_makespan_bound{0};

        /**
         * \name Why a candidate or a donor was passed over.
         */
        ///@{
        std::size_t declined_optional = 0;
        std::size_t declined_variable_arguments = 0;
        /// Covers already inside the support of something lifted earlier, which
        /// would re-derive it and waste the subproblems (paper, Example 12).
        std::size_t dropped_visited = 0;
        /// Constraints a donor's own row already implies term by term.
        std::size_t dropped_dominated = 0;
        std::size_t dropped_over_budget = 0;
        std::size_t declined_by_install = 0;
        ///@}
    };

    /**
     * \brief Infer `Cumulative` constraints with non-unit heights, by lifting
     * cover inequalities over a posted Cumulative's capacity rows, and post them
     * in derived mode.
     *
     * This is the second stage of Sidorov (CP 2026). A *cover* is a set of tasks
     * whose demands together overshoot a resource, so they cannot all run;
     * *lifting* then brings the remaining tasks in with the largest coefficients
     * that keep the inequality valid. The result, `sum_i pi_i a_i <= pi_0`, is a
     * statement about the resource that its own row does not make --- it holds
     * at every 0/1 point the row allows, but not over the rationals, which is
     * exactly what an integrality argument buys.
     *
     * What that is worth is *energy*. The tasks in a cut need `sum_i d_i pi_i`
     * units of a resource supplying `pi_0` per time step, and that ratio can
     * beat the donor row's own `sum_i d_i c_i / C`: three tasks of demand four
     * on a resource of capacity ten give a cut of `a + b + c <= 2`, worth three
     * halves against the row's six fifths. Where the ratio does *not* improve,
     * the cut is dropped, because the donor already said it better.
     *
     * **Expect no change from time-tabling.** A cut is valid, so every 0/1 point
     * the donor's row allows satisfies it too, and no verdict about one time
     * point can differ. It therefore ships with time-tabling off, as
     * InferredDisjunctive and CumulativeStrengthening do; a test asserting the
     * redundancy has to turn it back on.
     *
     * Restricted, as its stage in the plan is, to constant lengths, heights and
     * capacities, and to donors with no optional tasks.
     *
     * Nothing reaches the OPB. Every row of every posted constraint is
     * *derived*, by \ref validate_lifted_cover_cut and
     * \ref derive_lifted_cover_cut, which certify a cut by replaying the
     * knapsack dynamic programme that says it holds. That is complete by
     * construction, so the constraints coming from the published procedure
     * rather than from what happens to be easy to prove costs nothing:
     * \ref InferredCumulativeStats::cuts_uncertifiable is zero.
     *
     * \ingroup Presolvers
     */
    class InferredCumulative : public Presolver
    {
    private:
        std::shared_ptr<InferredCumulativeStats> _stats;
        std::size_t _max_covers;
        std::size_t _max_posted;
        std::size_t _maximum_capacity;
        std::size_t _max_lifting_calls;
        CumulativeRules _rules;
        InferredCumulativeMutation _mutation;
        std::optional<IntegerVariableID> _makespan;

    public:
        explicit InferredCumulative(std::shared_ptr<InferredCumulativeStats> stats = nullptr);

        /**
         * \brief Cap how many covers are grown and lifted, and how many of the
         * resulting cuts are posted.
         *
         * Sidorov's `N_cover` and `N_out`. Every drop is counted, because a
         * budget that quietly swallowed everything is indistinguishable, from
         * the outside, from a resource with nothing to find on it.
         */
        auto with_budgets(std::size_t max_covers, std::size_t max_posted) -> InferredCumulative &;

        /**
         * \brief The largest capacity an inferred constraint may have; a
         * thousand by default, which is what the paper's experiments used.
         *
         * The paper's `-b`. A cover of `k` tasks yields a right-hand side of
         * `k - 1`, so bounding the capacity bounds the cover size: one allows
         * binary covers only, two adds the pair-plus-a-third family, and three
         * or more turns on the equal-demand "long cover" rule as well. Lifting
         * is what grows a cover into a wide constraint, so this does not bound
         * the support.
         */
        auto with_maximum_capacity(std::size_t capacity) -> InferredCumulative &;

        /**
         * \brief How many lifting subproblems may be solved in total.
         *
         * The paper's `N_calls`, whose Appendix C setting is 2*10^4. Solving
         * these is the bottleneck of Algorithm 2, so the budget is against
         * them rather than against wall-clock.
         */
        auto with_lifting_call_budget(std::size_t calls) -> InferredCumulative &;

        /**
         * \brief Select which propagation rules the inferred constraints run.
         *
         * Energy only, by default, since a valid cut cannot change a
         * time-tabling verdict the donor's own row did not already reach.
         */
        auto with_rules(CumulativeRules rules) -> InferredCumulative &;

        /**
         * \brief Name the makespan, so that each posted cut also derives a
         * lower bound on it.
         *
         * A cut says its tasks cannot occupy more than `pi_0` of the resource
         * at once, and between them they need `sum_i d_i pi_i`, so no schedule
         * can be shorter than the ratio --- Sidorov's `L`, which
         * \ref InferredCumulativeStats::largest_capacity_bound reports and
         * which nothing in the proof otherwise says. With a makespan given, the
         * argument is made in the proof and the bound is inferred, so the
         * search starts from it and a `.pbp` contains it.
         *
         * The model must entail `start + length <= makespan` for every task of
         * every donor, which is what a scheduling model's makespan is for. That
         * is a promise, not something checkable from here; break it and VeriPB
         * refuses the derivation.
         */
        auto with_makespan(IntegerVariableID makespan) -> InferredCumulative &;

        /// Corrupt the certificate. For tests only, which assert that VeriPB
        /// rejects the result; see InferredCumulativeMutation.
        auto with_proof_mutation(InferredCumulativeMutation mutation) -> InferredCumulative &;

        [[nodiscard]] virtual auto run(Problem &, innards::Propagators &, innards::State &, innards::ProofLogger * const) -> bool override;
        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Presolver> override;
    };
}

#endif
