#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INFERRED_DISJUNCTIVE_INFERRED_DISJUNCTIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INFERRED_DISJUNCTIVE_INFERRED_DISJUNCTIVE_HH

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
     * \brief Deliberate corruptions of the assembled per-time certificate, for
     * testing only. VeriPB must reject each of them.
     *
     * The pieces this is built from each have their own mutations, and those
     * cover the pieces. What is left for these is the *assembly*: whether the
     * at-most-ones being merged really are about the tasks the clique claims,
     * whether the conclusion is the one the arithmetic supports, and whether a
     * pair that merely looks like a conflict can be smuggled in. Each of these
     * corrupts the conclusion rather than the route to it, since the route is
     * where a conflict-shaped derivation forgives everything.
     *
     * \ingroup Presolvers
     */
    namespace inferred_disjunctive_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Claim no member may run at all, rather than at most one.
        struct ClaimRhsZero
        {
        };

        /// Bridge one task's flags onto the *other* task's, so the at-most-one
        /// being merged is about a task the derivation never cornered.
        struct BridgeWrongTask
        {
        };

        /// Grow a clique with a task that does not conflict with its members ---
        /// the camouflage case, where a pair's demands sum to exactly the
        /// capacity and so are compatible by one unit. An off-by-one in the
        /// conflict test lands exactly here.
        struct IncludeNonConflicting
        {
        };

        /// Claim a makespan one larger than a posted clique's energy supports.
        /// The same discipline again, against the other thing a clique is used
        /// for: `L` is the number this whole exercise reports, so a derivation
        /// with slack in it would report it while proving something weaker.
        struct ClaimHigherMakespanBound
        {
        };
    }

    using InferredDisjunctiveMutation =
        std::variant<inferred_disjunctive_mutation::None, inferred_disjunctive_mutation::ClaimRhsZero, inferred_disjunctive_mutation::BridgeWrongTask,
            inferred_disjunctive_mutation::IncludeNonConflicting, inferred_disjunctive_mutation::ClaimHigherMakespanBound>;
    /**
     * \brief What the inferred-Disjunctive presolver did, filled in when it
     * runs.
     *
     * A presolver that found nothing writes nothing, removes no solution and
     * leaves every proof verifying, so the counts are what a test has to assert
     * on to tell "working" from "no-op". The drop counters matter as much as the
     * find ones: a budget that silently swallowed every candidate looks exactly
     * like a conflict graph with no cliques in it.
     *
     * \ingroup Presolvers
     */
    struct InferredDisjunctiveStats
    {
        /// Posted Cumulatives the presolver looked at.
        std::size_t donors_seen = 0;

        /// Distinct tasks across all of them, identified by start variable.
        std::size_t tasks = 0;

        /// Pairs of tasks that some resource cannot hold together.
        std::size_t conflicting_pairs = 0;

        /// Of those, the pairs whose conflict is witnessed only by a resource
        /// that does not contain both tasks' flags --- meaning the inference
        /// genuinely spans donors and needed bridging. Zero here on a
        /// single-resource model is the honest answer, and it is also how a
        /// test says a fixture is not exercising what it claims to.
        std::size_t cross_donor_pairs = 0;

        /// Maximal cliques the search produced, before ranking and budgeting.
        std::size_t cliques_found = 0;

        /// Cliques actually posted as derived Cumulatives: the number that
        /// matters.
        std::size_t cliques_posted = 0;

        /// Summed sizes of those, so a test can tell one clique of six from
        /// three of two.
        std::size_t clique_members_posted = 0;

        /**
         * \brief The largest capacity bound over the posted cliques: Sidorov's
         * `L`, and a lower bound on the makespan.
         *
         * A capacity-one Cumulative over a set of tasks says they must run one
         * after another, so the schedule cannot finish before their durations
         * summed. Sidorov reports this as `L = sum_i d_i pi_i / pi_0`; at the
         * unit coefficients this presolver deals in, `pi_0` is one and it is
         * just the clique's total duration --- which is already the metric the
         * cliques are ranked by, so this is that ranking's winning score.
         *
         * It is the number to compare against a published bound, and the only
         * output of this presolver that is meaningful without running a search.
         * Zero when nothing was posted.
         */
        Integer largest_capacity_bound{0};

        /**
         * \brief The largest makespan bound actually *derived*, over the posted
         * cliques, when a makespan variable was given.
         *
         * The certified counterpart of \ref largest_capacity_bound, and the one
         * that comes with a `.pbp`. It is usually the same number, and can be
         * larger: `L` assumes the tasks may start at time zero, while the
         * derivation argues over the window their earliest starts actually
         * leave them.
         *
         * Zero when no makespan was given, or when nothing was posted.
         */
        Integer certified_makespan_bound{0};

        /// Flag bridges emitted, one per (task, time) that had to be carried
        /// from a witnessing resource to the one holding the task's flags.
        std::size_t bridges_derived = 0;

        /**
         * \name Why a candidate or a donor was passed over.
         */
        ///@{
        std::size_t declined_optional = 0;
        std::size_t declined_variable_arguments = 0;
        std::size_t dropped_too_small = 0;
        std::size_t dropped_subset = 0;
        std::size_t dropped_over_budget = 0;
        std::size_t declined_by_install = 0;
        ///@}
    };

    /**
     * \brief Infer `Disjunctive` constraints --- capacity-one Cumulatives ---
     * from cliques in the conflict graph across all posted Cumulatives, and post
     * them in derived mode.
     *
     * Two tasks conflict if *some* resource cannot hold both at once, i.e. their
     * demands on it sum to more than its capacity. A set of tasks conflicting
     * pairwise can have at most one of them running at any time, whatever
     * resources the individual conflicts came from --- and when different pairs
     * conflict on different resources, that is an inference no single posted
     * Cumulative can make, which is the whole point.
     *
     * This is the first stage of Sidorov (CP 2026), restricted to what his own
     * data says carries most of the value: capacity one, unit coefficients. It
     * keeps every certificate polynomial. The general lifted case, with non-unit
     * coefficients, is InferredCumulative.
     *
     * Nothing reaches the OPB. Each clique is posted as a derived Cumulative
     * whose per-time rows are *proved*: the pairwise at-most-ones come out of a
     * witnessing resource's capacity row by weakening, saturating and dividing
     * by the margin; where the pair's witness is not where a task's flags live,
     * recover_conjunction_flag_bridge carries it across; and
     * recover_am1_from_pairs merges them into the clique inequality, which is
     * exactly a unit-height capacity-one row.
     *
     * **Expect no speedup from time-tabling.** A pair that conflicts is already
     * kept apart by whichever resource witnesses it, so the inferred
     * constraint's profile reasoning is redundant --- and it ships with
     * time-tabling off for that reason, exactly as CumulativeStrengthening does.
     * What is new is the *energy* argument over the clique: three pairwise
     * incompatible tasks of length three need nine units of a window that
     * supplies its width, which no single resource's capacity row says.
     *
     * \ingroup Presolvers
     */
    class InferredDisjunctive : public Presolver
    {
    private:
        std::shared_ptr<InferredDisjunctiveStats> _stats;
        std::size_t _max_candidates;
        std::size_t _max_posted;
        std::size_t _min_clique_size;
        CumulativeRules _rules;
        InferredDisjunctiveMutation _mutation;
        std::optional<IntegerVariableID> _makespan;

    public:
        explicit InferredDisjunctive(std::shared_ptr<InferredDisjunctiveStats> stats = nullptr);

        /**
         * \brief Cap how many candidate pairs are grown into cliques, and how
         * many of the results are posted.
         *
         * Sidorov's `N_cover` and `N_out`. The conflict graph can be dense, and
         * both the clique search and the per-time certificates cost real time
         * and real proof, so neither is allowed to run away. Every drop is
         * counted, because a budget that quietly swallowed everything is
         * indistinguishable from a model with nothing to find.
         */
        auto with_budgets(std::size_t max_candidates, std::size_t max_posted) -> InferredDisjunctive &;

        /**
         * \brief The smallest clique worth posting; three by default.
         *
         * A two-task "clique" is just a conflicting pair, which the resource
         * that witnesses it already rules out --- so posting one adds a
         * propagator that cannot infer anything new. Three is where the energy
         * argument starts to say something.
         */
        auto with_minimum_clique_size(std::size_t size) -> InferredDisjunctive &;

        /**
         * \brief Select which propagation rules the inferred constraints run.
         *
         * Energy only, by default, since their time-tabling is redundant with
         * the resources the conflicts came from. A test asserting that
         * redundancy has to turn time-tabling back on.
         */
        auto with_rules(CumulativeRules rules) -> InferredDisjunctive &;

        /**
         * \brief Name the makespan, so that each posted clique also derives a
         * lower bound on it.
         *
         * A clique's tasks run one after another, so the schedule cannot finish
         * before their durations summed --- which is what
         * \ref InferredDisjunctiveStats::largest_capacity_bound reports and what
         * nothing in the proof otherwise says. With a makespan given, the
         * argument is made in the proof and the bound is inferred.
         *
         * The model must entail `start + length <= makespan` for every task of
         * every donor. That is a promise, not something checkable from here;
         * break it and VeriPB refuses the derivation.
         */
        auto with_makespan(IntegerVariableID makespan) -> InferredDisjunctive &;

        /// Corrupt one step of the assembled certificate. For tests only, which
        /// assert that VeriPB rejects the result; see
        /// InferredDisjunctiveMutation.
        auto with_proof_mutation(InferredDisjunctiveMutation mutation) -> InferredDisjunctive &;

        [[nodiscard]] virtual auto run(Problem &, innards::Propagators &, innards::State &, innards::ProofLogger * const) -> bool override;
        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Presolver> override;
    };
}

#endif
