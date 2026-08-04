#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INFERRED_CUMULATIVE_INFERRED_CUMULATIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INFERRED_CUMULATIVE_INFERRED_CUMULATIVE_HH

#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/integer.hh>
#include <gcs/presolver.hh>

#include <cstddef>
#include <memory>
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

        /// Leave one of the donor's other tasks in the row rather than
        /// weakening it away, so the arithmetic runs on a degree that includes
        /// a demand the cut is not about.
        struct SkipAWeakening
        {
        };
    }

    using InferredCumulativeMutation = std::variant<inferred_cumulative_mutation::None, inferred_cumulative_mutation::ClaimTighterCapacity,
        inferred_cumulative_mutation::ClaimTallerTask, inferred_cumulative_mutation::SkipAWeakening>;

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

        /// Covers grown and then lifted, before ranking and budgeting.
        std::size_t covers_considered = 0;

        /// Lifted cuts that came out valid, certifiable, and worth more than
        /// the row they came from.
        std::size_t cuts_found = 0;

        /// Cuts actually posted as derived Cumulatives: the number that matters.
        std::size_t cuts_posted = 0;

        /// Of those, the ones with a coefficient above one --- the inference
        /// this stage adds over the capacity-one stage before it.
        std::size_t non_unit_cuts_posted = 0;

        /// Members brought into a cover by a lifting step, over all the covers
        /// considered. Zero here with cuts posted means every one of them is a
        /// plain cover inequality.
        std::size_t lifting_steps = 0;

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
         * \name Why a candidate or a donor was passed over.
         */
        ///@{
        std::size_t declined_optional = 0;
        std::size_t declined_variable_arguments = 0;
        std::size_t dropped_no_gain = 0;
        std::size_t dropped_subset = 0;
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
     * Nothing reaches the OPB. Each cut is grown *forward* by
     * \ref grow_lifted_cover_cut --- the arithmetic is run and the cut is
     * whatever comes out, so there is never a coefficient chosen first and
     * justified afterwards. Only the restrictions at the edges of a window are
     * a question for \ref plan_lifted_cover_cut, since there the heights are
     * already fixed and only the route may vary; a time point it cannot answer
     * declines the whole constraint rather than asserting anything.
     *
     * \ingroup Presolvers
     */
    class InferredCumulative : public Presolver
    {
    private:
        std::shared_ptr<InferredCumulativeStats> _stats;
        std::size_t _max_covers;
        std::size_t _max_posted;
        std::size_t _max_support;
        CumulativeRules _rules;
        InferredCumulativeMutation _mutation;

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
         * \brief The most tasks a single cut may span; twelve by default.
         *
         * Both ends of this are searches over subsets --- lifting order here,
         * covers again when the certificate is replayed at each time point ---
         * and a derived constraint over a resource's whole task list would make
         * both of them exponential for no gain, since the cuts worth having are
         * small.
         */
        auto with_maximum_support(std::size_t size) -> InferredCumulative &;

        /**
         * \brief Select which propagation rules the inferred constraints run.
         *
         * Energy only, by default, since a valid cut cannot change a
         * time-tabling verdict the donor's own row did not already reach.
         */
        auto with_rules(CumulativeRules rules) -> InferredCumulative &;

        /// Corrupt the certificate. For tests only, which assert that VeriPB
        /// rejects the result; see InferredCumulativeMutation.
        auto with_proof_mutation(InferredCumulativeMutation mutation) -> InferredCumulative &;

        [[nodiscard]] virtual auto run(Problem &, innards::Propagators &, innards::State &, innards::ProofLogger * const) -> bool override;
        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Presolver> override;
    };
}

#endif
