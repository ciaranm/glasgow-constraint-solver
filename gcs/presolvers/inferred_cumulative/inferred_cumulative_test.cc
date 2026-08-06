/* Inferring Cumulative constraints by lifting cover inequalities, following
 * Sidorov (CP 2026) Algorithms 1 and 2.
 *
 * The point of the exercise is a *certified reproduction*, so the constraints
 * are whatever the published procedure infers and not whatever happens to be
 * easy to prove. That makes the number this file cares most about the fraction
 * of inferred constraints a derivation was found for, which the verified sweep
 * reports and which the accounting assertion beside it keeps honest.
 *
 * The headline fixture is one task filling a resource of capacity five against
 * three of demand two, and its durations are load-bearing in a way that says
 * something about the published procedure: the cover of the three small tasks
 * has to outrank the ternary covers containing the big one, or Algorithm 2's
 * visited-cover rule skips it and no coefficient above one is ever produced.
 * See lifted_instance() for the two inequalities the durations must satisfy.
 *
 * That fixture is also the differential pair the issue asks for. Its conflict
 * graph is a star --- the big task fights each small one, no two small ones
 * fight each other --- so it holds no clique of three, and the capacity-one
 * stage before this one has nothing to post. Both configurations are run below
 * and the difference is asserted, rather than the non-unit case being taken on
 * trust.
 *
 * The signature test of a lifted constraint is that claiming one better must
 * fail: with small, close-together integers a derivation that landed somewhere
 * weaker than intended still lands somewhere true, and only a `+1` that veripb
 * *refuses* says the honest line is tight to what the constraint assumes of it.
 * Both directions are mutated here --- one less capacity, one more height ---
 * over a fixture carrying a spare task, so that the row the certificate runs on
 * has something in it the cut is not about. A third mutation corrupts the
 * derivation rather than the claim, by building the certificate's dynamic
 * programme against capacities one below the rows'.
 *
 * Then all of that again over two resources, which is what Equation 4's lifting
 * is actually over. That fixture's cut is a consequence of both rows and of
 * neither alone, so nothing in the single-resource cases reaches the machinery
 * it needs: a weight per resource in the programme, and each resource's row
 * carried onto the members' own flags before any of them can be put in the same
 * derivation. `BridgeWrongTask` is the mutation that only exists there --- with
 * one resource there is no crossing to corrupt --- and the verified sweep draws
 * one to three resources so that veripb sees the crossing across many shapes
 * rather than only over the fixture built to need it.
 */

#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/presolvers/inferred_cumulative.hh>
#include <gcs/presolvers/inferred_disjunctive.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <random>
#include <set>
#include <string>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using std::cerr;
using std::ifstream;
using std::make_optional;
using std::make_shared;
using std::move;
using std::nullopt;
using std::optional;
using std::set;
using std::shared_ptr;
using std::string;
using std::to_string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

namespace
{
    auto fail(const string & message) -> void
    {
        println(cerr, "inferred cumulative test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    /// A further resource over the same tasks: what each takes of it, and how
    /// much of it there is.
    struct Resource
    {
        vector<Integer> demands;
        Integer capacity;
    };

    /// A task list with lengths and a horizon, and one or more resources over
    /// it. More than one is what Equation 4's lifting is for, and is posted as
    /// one Cumulative apiece --- which is also how Sidorov's own preprocessor
    /// builds an RCPSP.
    struct Instance
    {
        vector<Integer> demands, lengths;
        Integer capacity;
        int horizon;

        /// Latest start per task, where it is tighter than the horizon allows.
        /// Empty means `horizon - length` for everyone --- which gives every
        /// task the window `[0, horizon - 1]` whatever its length, so a fixture
        /// leaving this empty exercises none of the window-edge restriction.
        vector<int> latest_start = {};

        /// Resources beyond the first.
        vector<Resource> also = {};

        [[nodiscard]] auto resources() const -> vector<Resource>
        {
            vector<Resource> all{Resource{demands, capacity}};
            all.insert(all.end(), also.begin(), also.end());
            return all;
        }

        [[nodiscard]] auto latest(std::size_t i) const -> int
        {
            return latest_start.empty() ? horizon - lengths[i].raw_value : latest_start[i];
        }
    };

    /// The headline fixture: one task filling a resource of capacity five, and
    /// three of demand two which fit in pairs but not in threes.
    ///
    /// The durations are what make this the fixture it is. Algorithm 1 ranks
    /// covers by the capacity bound of their own cover inequality, and
    /// Algorithm 2 then refuses to lift a cover whose members a previous
    /// lifting already brought together. So the equal-demand cover of the three
    /// small tasks has to outrank the ternary covers containing the big one, or
    /// it is skipped before it is ever lifted and no coefficient above one is
    /// produced at all. That needs `d_big < d_small`. Meanwhile the cut only
    /// bites on a horizon the donor's own energy check clears, which needs
    /// `2 d_big > d_small`. Three against five satisfies both; four equal
    /// durations satisfies neither, which is why the obvious version of this
    /// fixture finds nothing. That is a property of the published procedure,
    /// not of this implementation.
    auto lifted_instance(int horizon) -> Instance
    {
        return Instance{{5_i, 2_i, 2_i, 2_i}, {3_i, 5_i, 5_i, 5_i}, 5_i, horizon};
    }

    /// The same, plus a task the cut does not reach, so that the donor's row
    /// always carries a term the cut is not about.
    auto lifted_instance_with_spare(int horizon) -> Instance
    {
        return Instance{{5_i, 2_i, 2_i, 2_i, 1_i}, {3_i, 5_i, 5_i, 5_i, 1_i}, 5_i, horizon};
    }

    /// One whose equal-demand family is a cover of *four* tasks: four demands of
    /// two overshoot a capacity of seven, and five of them are there for the
    /// longest and the shortest four to be different sets. That size is what
    /// survives the budget being applied a second time across the resources.
    auto long_cover_instance(int horizon) -> Instance
    {
        return Instance{{5_i, 2_i, 2_i, 2_i, 2_i, 2_i}, {3_i, 6_i, 5_i, 5_i, 5_i, 4_i}, 7_i, horizon};
    }

    /// Two resources, and a cut that is a consequence of both of them and of
    /// neither alone. This is what Equation 4's lifting is for, and nothing in
    /// the single-resource fixtures above reaches it.
    ///
    /// The two rows do different halves of the work, which is the point. The
    /// cover `{0, 1, 2}` belongs to the *second* resource --- two and three and
    /// one overshoot its five --- and is no cover of the first, where the same
    /// three tasks come to exactly its three. Lifting the fourth task then asks
    /// what those three can still weigh once it is running, and the answer comes
    /// from the *first* resource, which the fourth task fills on its own, so
    /// nothing else can run beside it and the coefficient is two rather than
    /// one.
    ///
    /// So `a0 + a1 + a2 + 2 a3 <= 2` needs both rows and each for a different
    /// reason: the second is what refuses `{0, 1, 2}` and the first is what
    /// refuses `{1, 3}`. Its energy is fifteen against a capacity of two, so no
    /// schedule is shorter than eight --- which is the optimum, while the best
    /// either row reaches on its own is seven.
    auto two_resource_instance(int horizon) -> Instance
    {
        return Instance{{1_i, 1_i, 1_i, 3_i}, {2_i, 5_i, 4_i, 2_i}, 3_i, horizon, {}, {Resource{{2_i, 3_i, 1_i, 2_i}, 5_i}}};
    }

    enum struct Stage
    {
        none,
        disjunctive,
        cumulative
    };

    struct Setup
    {
        Stage stage = Stage::cumulative;
        CumulativeRules rules = CumulativeRules{};
        optional<CumulativeRules> inferred_rules = nullopt;
        std::size_t max_covers = 100, max_posted = 5;
        InferredCumulativeMutation mutation = inferred_cumulative_mutation::None{};
        shared_ptr<InferredCumulativeStats> stats = nullptr;
        shared_ptr<InferredDisjunctiveStats> disjunctive_stats = nullptr;

        /// Add a makespan variable, the `start_i + length_i <= makespan` rows
        /// that make it one, and minimise it --- so that the cut's capacity
        /// bound is not only reported but derived, and the search starts from
        /// it.
        bool minimise_makespan = false;
    };

    auto post(Problem & p, const Instance & instance, const Setup & setup) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts;
        for (std::size_t i = 0; i < instance.demands.size(); ++i)
            starts.push_back(p.create_integer_variable(0_i, Integer{instance.latest(i)}, "s" + to_string(i)));

        optional<IntegerVariableID> makespan;
        if (setup.minimise_makespan) {
            makespan = p.create_integer_variable(0_i, Integer{instance.horizon}, "makespan");
            for (std::size_t i = 0; i < starts.size(); ++i)
                p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * *makespan + -1_i * starts[i], instance.lengths[i]});
            p.minimise(*makespan);
        }

        for (const auto & resource : instance.resources())
            p.post(Cumulative{starts, instance.lengths, resource.demands, resource.capacity}.with_rules(setup.rules));

        switch (setup.stage) {
            using enum Stage;
        case none: break;
        case disjunctive: {
            auto presolver = InferredDisjunctive{setup.disjunctive_stats};
            if (setup.inferred_rules)
                presolver.with_rules(*setup.inferred_rules);
            p.add_presolver(presolver);
        } break;
        case cumulative: {
            auto presolver = InferredCumulative{setup.stats};
            presolver.with_budgets(setup.max_covers, setup.max_posted).with_proof_mutation(setup.mutation);
            if (setup.inferred_rules)
                presolver.with_rules(*setup.inferred_rules);
            if (makespan)
                presolver.with_makespan(*makespan);
            p.add_presolver(presolver);
        } break;
        }
        return starts;
    }

    struct Outcome
    {
        set<vector<int>> solutions;
        unsigned long long recursions = 0;
        bool refuted_at_root = false;
        /// The best objective reported, when the setup minimises a makespan.
        optional<Integer> best_makespan;
    };

    auto solve_instance(const Instance & instance, const Setup & setup, const optional<string> & proof_name, bool verify = true) -> Outcome
    {
        Problem p;
        auto starts = post(p, instance, setup);

        Outcome outcome;
        bool reached_a_node = false, found_a_solution = false;
        auto stats = solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               found_a_solution = true;
                               vector<int> solution;
                               for (const auto & v : starts)
                                   solution.push_back(s(v).raw_value);
                               outcome.solutions.insert(move(solution));
                               if (setup.minimise_makespan) {
                                   Integer end = 0_i;
                                   for (std::size_t i = 0; i < starts.size(); ++i)
                                       end = std::max(end, s(starts[i]) + instance.lengths[i]);
                                   outcome.best_makespan = end;
                               }
                               return true;
                           },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    return true;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);

        outcome.recursions = stats.recursions;
        outcome.refuted_at_root = ! reached_a_node && ! found_a_solution;

        if (proof_name && verify)
            verify_proof_and_clean_up(*proof_name);
        return outcome;
    }

    /// Brute force over the same instance: every start assignment whose profile
    /// stays under the capacity at every time point.
    auto expected_solutions(const Instance & instance) -> set<vector<int>>
    {
        auto n = instance.demands.size();
        set<vector<int>> expected;
        vector<int> current(n, 0);
        auto resources = instance.resources();
        auto ok = [&]() {
            for (int t = 0; t < instance.horizon; ++t)
                for (const auto & resource : resources) {
                    Integer load = 0_i;
                    for (std::size_t i = 0; i < n; ++i)
                        if (t >= current[i] && t < current[i] + instance.lengths[i].raw_value)
                            load += resource.demands[i];
                    if (load > resource.capacity)
                        return false;
                }
            return true;
        };
        auto recurse = [&](auto && self, std::size_t at) -> void {
            if (at == n) {
                if (ok())
                    expected.insert(current);
                return;
            }
            for (int s = 0; s <= instance.latest(at); ++s) {
                current[at] = s;
                self(self, at + 1);
            }
        };
        recurse(recurse, 0);
        return expected;
    }

    auto read_file(const string & name) -> string
    {
        ifstream in{name, std::ios::binary};
        if (! in)
            fail("could not read " + name);
        return string{std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
    }

    auto count_occurrences(const string & haystack, const string & needle) -> std::size_t
    {
        std::size_t count = 0;
        for (auto at = haystack.find(needle); at != string::npos; at = haystack.find(needle, at + needle.size()))
            ++count;
        return count;
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);
    auto proofs = can_run_veripb();

    // The tasks need forty-five units of a resource that supplies five a step,
    // so the donor's own energy check is content with a horizon of ten; the
    // lifted cut needs twenty-one units of a supply of two, and is not.
    {
        auto stats = make_shared<InferredCumulativeStats>();

        auto donor_only = solve_instance(lifted_instance(10), Setup{.stage = Stage::none}, nullopt);
        if (donor_only.refuted_at_root)
            fail("the donor alone refuted at the root, so the fixture proves nothing");

        auto lifted = solve_instance(lifted_instance(10), Setup{.stats = stats}, proofs ? make_optional("inferred_cumulative_unsat") : nullopt);

        if (stats->non_unit_cuts_posted != 1)
            fail("posted " + to_string(stats->non_unit_cuts_posted) + " cuts with a coefficient above one, not the one the fixture is about");
        // Sidorov's L for that cut: 2*3 + 1*5*3 = 21 units of a resource
        // supplying 2 per step, so no schedule can finish before 11.
        if (stats->largest_capacity_bound != 11_i)
            fail("reported a makespan bound of " + to_string(stats->largest_capacity_bound.raw_value) + ", not the eleven the cut carries");
        if (stats->lifting_subproblems == 0)
            fail("no lifting subproblem was solved, so nothing was lifted");
        if (! lifted.refuted_at_root)
            fail("the lifted cut did not refute at the root");
        if (! lifted.solutions.empty())
            fail("the instance is unsatisfiable but solutions were reported");

        println(cerr, "lifted cut: refuted at the root against {} nodes without it, {} constraints inferred, bound {}", donor_only.recursions,
            stats->cuts_found, stats->largest_capacity_bound.raw_value);
    }

    // The differential pair. The conflict graph here is a star, so there is no
    // clique of three to find and the capacity-one stage posts nothing --- this
    // instance is closed by a non-unit coefficient or not at all.
    {
        auto stats = make_shared<InferredDisjunctiveStats>();
        auto disjunctive_only = solve_instance(lifted_instance(10), Setup{.stage = Stage::disjunctive, .disjunctive_stats = stats}, nullopt);

        if (stats->conflicting_pairs != 3)
            fail("differential pair: found " + to_string(stats->conflicting_pairs) + " conflicting pairs, not the three of the star");
        if (stats->cliques_posted != 0)
            fail("differential pair: the capacity-one stage posted something, so the comparison is not about lifting");
        if (disjunctive_only.refuted_at_root)
            fail("differential pair: the capacity-one stage refuted at the root, so it did not need this one");
        println(cerr, "differential pair: capacity-one inference finds no clique and does not refute");
    }

    // The bound in the proof rather than only in the stats. With the makespan
    // named, the presolver derives its `L` instead of reporting it, the search
    // starts from it, and the branch-and-bound proof closes against a lower
    // bound VeriPB has checked.
    //
    // Eleven against an optimum of thirteen, which is the shape of the whole
    // exercise: `L` is a relaxation bound and is not expected to be tight. What
    // *is* asserted is the validation the artefact runs --- a bound above a
    // feasible makespan would be a bug, and this fixture knows its optimum. The
    // margin-of-one fixture that says the arithmetic is tight, and the
    // mutations that say so by being refused, are in
    // derived_cumulative_test.cc.
    {
        auto stats = make_shared<InferredCumulativeStats>();
        auto certified = solve_instance(
            lifted_instance(13), Setup{.stats = stats, .minimise_makespan = true}, proofs ? make_optional("inferred_cumulative_makespan") : nullopt);

        if (stats->largest_capacity_bound != 11_i)
            fail("certified bound: reported an L of " + to_string(stats->largest_capacity_bound.raw_value) + ", not eleven");
        if (stats->certified_makespan_bound != 11_i)
            fail("certified bound: derived a makespan bound of " + to_string(stats->certified_makespan_bound.raw_value) +
                ", not the eleven the cut's capacity bound carries");
        if (certified.best_makespan != make_optional(13_i))
            fail("certified bound: the optimum is " +
                (certified.best_makespan ? to_string(certified.best_makespan->raw_value) : string{"unreachable"}) + ", not the thirteen expected");
        if (*certified.best_makespan < stats->certified_makespan_bound)
            fail("certified bound: derived a bound above a schedule that exists");

        // The same number with proofs off, or the solver is doing different
        // arithmetic depending on whether anyone is watching.
        auto unproved_stats = make_shared<InferredCumulativeStats>();
        solve_instance(lifted_instance(13), Setup{.stats = unproved_stats, .minimise_makespan = true}, nullopt);
        if (unproved_stats->certified_makespan_bound != stats->certified_makespan_bound)
            fail("certified bound: the bound differs with proofs off");

        println(cerr, "certified makespan bound: derived {}, optimum {}, over {} nodes", stats->certified_makespan_bound.raw_value,
            certified.best_makespan->raw_value, certified.recursions);
    }

    // Twelve time points, where the tasks fit: the big one alone, then two of
    // the small ones, then the last. Still satisfiable, still every solution,
    // and the cut is still posted --- an inferred constraint has to be harmless
    // where it is not decisive.
    {
        auto stats = make_shared<InferredCumulativeStats>();
        auto lifted = solve_instance(lifted_instance(13), Setup{.stats = stats}, proofs ? make_optional("inferred_cumulative_sat") : nullopt);

        if (stats->non_unit_cuts_posted != 1)
            fail("sharp twin: the lifted cut was not posted, so the comparison is vacuous");
        auto expected = expected_solutions(lifted_instance(13));
        if (expected.empty())
            fail("sharp twin: the fixture has no solutions, so it is not the twin it claims to be");
        if (lifted.solutions != expected)
            fail("sharp twin: solutions do not match brute force, so the cut removed some");
        println(cerr, "sharp twin: {} solutions, matching brute force", lifted.solutions.size());
    }

    // Solution preservation at several shapes, including the spare-task one,
    // where the cut spans some of the resource rather than all of it.
    for (const auto & instance : {lifted_instance(14), lifted_instance_with_spare(13), Instance{{4_i, 4_i, 4_i}, {3_i, 3_i, 3_i}, 10_i, 7}}) {
        auto stats = make_shared<InferredCumulativeStats>();
        auto lifted = solve_instance(instance, Setup{.stats = stats}, nullopt);
        auto expected = expected_solutions(instance);
        if (lifted.solutions != expected)
            fail("solution preservation: " + to_string(instance.demands.size()) + " tasks into a horizon of " + to_string(instance.horizon) +
                " does not match brute force");
    }
    println(cerr, "solution preservation: three shapes match brute force");

    // A cardinality cut, with no conflicting pair anywhere in it: three tasks
    // of demand four on a resource of capacity ten fit in twos and not in
    // threes, which nothing assembled out of pairwise at-most-ones can say.
    {
        auto stats = make_shared<InferredCumulativeStats>();
        const Instance cardinality{{4_i, 4_i, 4_i}, {3_i, 3_i, 3_i}, 10_i, 7};
        solve_instance(cardinality, Setup{.stats = stats}, proofs ? make_optional("inferred_cumulative_cardinality") : nullopt);
        if (stats->cuts_posted != 1)
            fail("cardinality: posted " + to_string(stats->cuts_posted) + " cuts, not the one over the three tasks");
        if (stats->non_unit_cuts_posted != 0)
            fail("cardinality: the cut has a coefficient above one, so it is not the unit-coefficient case");
        // Nine units of work against a supply of two per step.
        if (stats->largest_capacity_bound != 5_i)
            fail("cardinality: reported a bound of " + to_string(stats->largest_capacity_bound.raw_value) + ", not five");
        println(cerr, "cardinality cut: posted over three mutually compatible tasks, bound 5");
    }

    // The window edges, which is the only place a programme is built over
    // fewer than all of the members. Pinning the big task into the first half of the horizon leaves
    // the second half holding only the three small ones, so those time points
    // need `b + c + d <= 2` --- the same cut over fewer members, with the same
    // coefficients, since a Cumulative has one height per task and they cannot
    // move to suit a time point.
    //
    // Without this the presolver's tests say nothing about that path at all:
    // a task whose start domain is `[0, horizon - length]` has the window
    // `[0, horizon - 1]` however long it is, so every other fixture here has
    // all its members present at every time point.
    {
        auto stats = make_shared<InferredCumulativeStats>();
        auto instance = lifted_instance(13);
        // Every task a different window, so that *whatever* cut Algorithm 2
        // picks, its members do not all appear at the same time points. Pinning
        // only one task makes this fixture depend on that task being in the
        // posted cut, which is not something the test should be asserting by
        // accident --- it went quiet on one platform for exactly that reason.
        instance.latest_start = {2, 4, 6, 8};
        auto lifted = solve_instance(instance, Setup{.stats = stats}, proofs ? make_optional("inferred_cumulative_edges") : nullopt);

        if (stats->non_unit_cuts_posted != 1)
            fail("window edges: the lifted cut was not posted, so the restriction is not being exercised");
        // Only when a proof was asked for. No row is derived at all with proofs
        // off --- install_derived_cumulative runs a recipe only when there is a
        // logger --- so the count is zero for a reason that says nothing about
        // windows. That is what turned the Windows lane red: `can_run_veripb()`
        // shells out to `veripb --help >/dev/null`, which cmd.exe cannot
        // redirect, so that platform takes the proofs-off path throughout.
        if (proofs && 0 == stats->restricted_rows_rebuilt)
            fail("window edges: every time point had all four members, so no restricted programme was ever built");
        auto expected = expected_solutions(instance);
        if (expected.empty())
            fail("window edges: the fixture has no solutions, so it says nothing about preservation");
        if (lifted.solutions != expected)
            fail("window edges: solutions do not match brute force");
        println(cerr, "window edges: {} restricted rows rebuilt, {} solutions matching brute force", stats->restricted_rows_rebuilt,
            lifted.solutions.size());
    }

    // And the fixtures that do *not* restrict say so, rather than leaving it
    // ambiguous whether the path ran.
    {
        auto stats = make_shared<InferredCumulativeStats>();
        solve_instance(lifted_instance(13), Setup{.stats = stats}, nullopt);
        if (stats->restricted_rows_rebuilt != 0)
            fail("uniform windows: something was restricted, so the fixture above is not the one testing that");
    }

    // Time-table neutrality. A cut is *valid*, so every occupancy point the
    // donor's row allows satisfies it too, and no verdict about a single time
    // point can differ. With the energy rules off everywhere the node counts
    // must be identical.
    {
        const CumulativeRules tt_only{.time_table = true, .overload = false, .profile_overload = false};
        auto stats = make_shared<InferredCumulativeStats>();

        auto without = solve_instance(lifted_instance(13), Setup{.stage = Stage::none, .rules = tt_only}, nullopt);
        auto with = solve_instance(lifted_instance(13), Setup{.rules = tt_only, .inferred_rules = make_optional(tt_only), .stats = stats}, nullopt);

        if (stats->cuts_posted == 0)
            fail("neutrality: nothing was posted, so the comparison is vacuous");
        if (without.solutions != with.solutions)
            fail("neutrality: the solution set changed");
        if (without.recursions != with.recursions)
            fail("neutrality: " + to_string(with.recursions) + " nodes against " + to_string(without.recursions) +
                " --- the cut changed what time-tabling permits, which means it is not implied");
        println(cerr, "neutrality: {} nodes either way", with.recursions);
    }

    // Budgets, and that they are counted rather than silent.
    {
        auto unbounded = make_shared<InferredCumulativeStats>();
        solve_instance(lifted_instance(13), Setup{.stats = unbounded}, nullopt);
        auto stats = make_shared<InferredCumulativeStats>();
        solve_instance(lifted_instance(13), Setup{.max_covers = 0, .stats = stats}, nullopt);
        if (stats->covers_considered >= unbounded->covers_considered)
            fail("a zero cover budget considered " + to_string(stats->covers_considered) + " covers against " +
                to_string(unbounded->covers_considered) + " unbounded, so the budget did not bite");
    }
    {
        // The cover budget bites twice, and what survives both is a cover of
        // *more* than three tasks: the equal-demand families are added after
        // each resource's own budget, and the merge across resources then keeps
        // every large cover outright and only the best `max_covers` of the rest.
        // A long cover of exactly three does not survive a budget of zero, which
        // is why this fixture's five demand-two tasks under a capacity of seven
        // are five and not four.
        auto stats = make_shared<InferredCumulativeStats>();
        solve_instance(long_cover_instance(13), Setup{.max_covers = 0, .stats = stats}, nullopt);
        if (stats->covers_considered == 0)
            fail("a zero cover budget dropped the long covers too, which survive it");
    }
    {
        auto stats = make_shared<InferredCumulativeStats>();
        solve_instance(lifted_instance_with_spare(13), Setup{.max_posted = 0, .stats = stats}, nullopt);
        if (stats->cuts_posted != 0)
            fail("a zero output budget still posted a cut");
        if (stats->dropped_over_budget == 0)
            fail("a zero output budget dropped cuts without counting them");
        // Nothing posted has to mean no bound claimed: a stale bound would be a
        // lower bound nobody derived.
        if (stats->largest_capacity_bound != 0_i)
            fail("posted no cut but still reported a bound of " + to_string(stats->largest_capacity_bound.raw_value));
    }
    println(cerr, "budgets: both caps bite, and both are counted");

    // Random instances against brute force, with demands drawn against each
    // instance's own capacity rather than from a fixed pool. A task above half
    // the capacity is the one that lifts into a cover of small tasks with a
    // coefficient above one, so drawing one deliberately is how the non-unit
    // case gets a turn at all --- with a fixed pool it happens by accident and
    // the corpus is seed-flaky about whether it happened.
    //
    // Latest starts are drawn too, and for the same kind of reason: leaving
    // them at `horizon - length` gives every task the window `[0, horizon - 1]`
    // however long it is, so a corpus built that way never restricts a row to
    // fewer members and never builds a restricted programme.
    {
        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(3, 5), cap_dist(4, 12), len_dist(1, 3), tall_dist(0, 2), pin_dist(0, 2);

        // The three "it actually fired" assertions below are the only ones with
        // any power over a presolver --- doing nothing preserves every solution
        // and verifies every proof --- but over a fixed draw they are assertions
        // about the *draw*: seed 905208 posts no non-unit cut in sixty
        // instances, and CI eventually meets such a seed. So draw until they
        // fire, up to a cap, which leaves the common case at sixty and turns the
        // assertion into "the generator cannot produce one in 240 goes".
        std::size_t posted = 0, non_unit = 0, steps = 0, restricted = 0;
        int drawn = 0;
        for (; drawn < 240 && (drawn < 60 || 0 == posted || 0 == non_unit || 0 == steps); ++drawn) {
            auto capacity = cap_dist(rand);
            Instance instance{{}, {}, Integer{capacity}, 0};
            std::uniform_int_distribution<> tall(capacity / 2 + 1, capacity), rest(1, capacity / 2);

            auto n = n_dist(rand);
            int longest = 0;
            for (int i = 0; i < n; ++i) {
                auto length = len_dist(rand);
                longest = std::max(longest, length);
                instance.lengths.push_back(Integer{length});
                instance.demands.push_back(Integer{0 == tall_dist(rand) ? tall(rand) : rest(rand)});
            }
            // Enough horizon that every task can move, and little enough that
            // the enumeration stays small.
            instance.horizon = longest + 2;
            for (int i = 0; i < n; ++i) {
                auto latest = static_cast<int>(instance.horizon - instance.lengths[i].raw_value);
                instance.latest_start.push_back(0 == pin_dist(rand) && latest > 0 ? latest - 1 : latest);
            }

            auto stats = make_shared<InferredCumulativeStats>();
            auto lifted = solve_instance(instance, Setup{.stats = stats}, nullopt);
            if (lifted.solutions != expected_solutions(instance)) {
                println(cerr, "demands={} lengths={} capacity={} horizon={}", instance.demands, instance.lengths, instance.capacity.raw_value,
                    instance.horizon);
                fail("the inferred cut removed solutions");
            }
            posted += stats->cuts_posted;
            non_unit += stats->non_unit_cuts_posted;
            steps += stats->lifting_subproblems;
            restricted += stats->restricted_rows_rebuilt;
        }

        if (posted == 0)
            fail("the presolver posted nothing across " + to_string(drawn) + " random instances, so it checked nothing");
        if (non_unit == 0)
            fail("no cut across " + to_string(drawn) + " random instances had a coefficient above one, so the lifting checked nothing");
        if (steps == 0)
            fail("no lifting subproblem was solved across " + to_string(drawn) + " random instances");
        // Not asserted here: with proofs off the recipe never runs, so no row
        // is derived and nothing is restricted whatever the windows do. That
        // belongs to the verified sweep below.
        if (restricted != 0)
            fail("rows were derived with proofs off, which means work is being done that nothing will check");
        println(
            cerr, "solution preservation: {} cuts over {} random instances ({} non-unit), {} lifting subproblems", posted, drawn, non_unit, steps);
    }

    // An optional-task donor is declined loudly rather than mis-derived.
    {
        auto stats = make_shared<InferredCumulativeStats>();
        Problem p;
        vector<IntegerVariableID> starts, presences;
        for (int i = 0; i < 4; ++i) {
            starts.push_back(p.create_integer_variable(0_i, 3_i));
            presences.push_back(p.create_integer_variable(0_i, 1_i));
        }
        vector<IntegerVariableID> lengths(4, constant_variable(2_i)),
            heights{constant_variable(5_i), constant_variable(2_i), constant_variable(2_i), constant_variable(2_i)};
        p.post(Cumulative{starts, lengths, heights, presences, constant_variable(5_i)});
        p.add_presolver(InferredCumulative{stats});
        solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, nullopt);

        if (stats->declined_optional != 1)
            fail("an optional-task donor was not declined");
        if (stats->cuts_posted != 0)
            fail("an optional-task donor was used anyway");
        println(cerr, "an optional-task donor is declined");
    }

    if (! proofs) {
        println(cerr, "veripb is not available, so the proof-level checks are skipped");
        return EXIT_SUCCESS;
    }

    // The corpus again with proofs on, which is the only way the certificate
    // gets a turn: with proofs off no row is derived at all, so everything
    // above says nothing about whether the arithmetic is right. Windows are
    // deliberately ragged, so that veripb sees restricted rows across many
    // shapes rather than only the hand-built fixture.
    {
        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(3, 5), rows_dist(1, 3), cap_dist(4, 10), len_dist(1, 3), tall_dist(0, 2), pin_dist(0, 1);

        std::size_t posted = 0, restricted = 0, inferred = 0, uncertifiable = 0, over_budget = 0, declined = 0, over_state_budget = 0,
                    subproblems_over_budget = 0, multi_resource = 0;
        for (int k = 0; k < 25; ++k) {
            // One to three resources over the same tasks, so that the crossing
            // is exercised over many shapes rather than only over the fixture
            // built to need it --- and so that a cut whose certificate cites two
            // rows is checked by veripb rather than argued about.
            auto rows = rows_dist(rand);
            auto n = n_dist(rand);

            Instance instance{{}, {}, 0_i, 0};
            int longest = 0;
            for (int i = 0; i < n; ++i) {
                auto length = len_dist(rand);
                longest = std::max(longest, length);
                instance.lengths.push_back(Integer{length});
            }
            instance.horizon = longest + 3;
            for (int i = 0; i < n; ++i) {
                auto latest = static_cast<int>(instance.horizon - instance.lengths[i].raw_value);
                instance.latest_start.push_back(0 == pin_dist(rand) && latest > 1 ? latest - 1 : latest);
            }

            for (int row = 0; row < rows; ++row) {
                auto capacity = cap_dist(rand);
                std::uniform_int_distribution<> tall(capacity / 2 + 1, capacity), rest(1, capacity / 2);
                vector<Integer> demands;
                for (int i = 0; i < n; ++i)
                    demands.push_back(Integer{0 == tall_dist(rand) ? tall(rand) : rest(rand)});
                if (0 == row) {
                    instance.demands = move(demands);
                    instance.capacity = Integer{capacity};
                }
                else
                    instance.also.push_back(Resource{move(demands), Integer{capacity}});
            }

            auto stats = make_shared<InferredCumulativeStats>();
            auto lifted = solve_instance(instance, Setup{.stats = stats}, make_optional("inferred_cumulative_sweep"));
            if (lifted.solutions != expected_solutions(instance)) {
                println(cerr, "demands={} lengths={} capacity={} horizon={} latest={} extra rows={}", instance.demands, instance.lengths,
                    instance.capacity.raw_value, instance.horizon, instance.latest_start, instance.also.size());
                fail("the verified sweep lost solutions");
            }
            posted += stats->cuts_posted;
            restricted += stats->restricted_rows_rebuilt;
            inferred += stats->cuts_found;
            uncertifiable += stats->cuts_uncertifiable;
            over_budget += stats->dropped_over_budget;
            declined += stats->declined_by_install;
            over_state_budget += stats->dropped_over_state_budget;
            subproblems_over_budget += stats->lifting_subproblems_over_budget;
            multi_resource += stats->multi_resource_cuts_posted;
        }

        if (posted == 0)
            fail("the verified sweep posted nothing, so veripb checked no certificate of ours");
        if (restricted == 0)
            fail("no row in the verified sweep was restricted to fewer members, so no restricted programme was ever built");
        // Every constraint Algorithm 2 inferred was posted, dropped by the
        // output budget before anyone asked about proving it, dropped for want
        // of a derivation, or declined by the install. If those do not add up,
        // something else is happening to constraints and the certified fraction
        // means nothing.
        if (posted + uncertifiable + over_budget + declined + over_state_budget != inferred)
            fail("the sweep inferred " + to_string(inferred) + " constraints but accounts for " + to_string(posted) + " posted, " +
                to_string(uncertifiable) + " uncertifiable, " + to_string(over_budget) + " over budget, " + to_string(over_state_budget) +
                " over the state budget and " + to_string(declined) + " declined");
        // And the certified fraction is all of it. This is the whole point of
        // certifying by replaying the lifting procedure's own knapsack
        // programme: it is complete by construction, where the cutting-planes
        // search it replaced dropped about one constraint in twenty-five.
        if (uncertifiable != 0)
            fail("the sweep could not derive " + to_string(uncertifiable) + " constraints, which the dynamic programme should make impossible");
        // The state budget is there for a pathology, not for these: a programme
        // it stops is a cut this could probably have certified, and one it stops
        // during lifting is a coefficient the published procedure would have
        // found. Either happening at these sizes means the budget is wrong.
        if (over_state_budget != 0 || subproblems_over_budget != 0)
            fail("the sweep hit the state budget " + to_string(over_state_budget) + " times certifying and " + to_string(subproblems_over_budget) +
                " times lifting, at sizes where it should never be reached");
        // And the multi-resource path is genuinely being checked here rather
        // than only by the fixture built for it.
        if (multi_resource == 0)
            fail("no cut in the verified sweep needed more than one row, so veripb checked no crossing");
        auto attempted = inferred - over_budget;
        println(cerr, "verified sweep: {} of {} attempted constraints certified ({} over more than one row), {} rows restricted", posted, attempted,
            multi_resource, restricted);
    }

    // Nothing may have reached the OPB: the whole plan turns on an inferred
    // constraint being a derivation rather than a model axiom.
    {
        const string with = "inferred_cumulative_opb_with", without = "inferred_cumulative_opb_without";
        for (const auto & [name, stage] : {std::pair{with, Stage::cumulative}, std::pair{without, Stage::none}}) {
            Problem p;
            post(p, lifted_instance(13), Setup{.stage = stage});
            solve_with(
                p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, make_optional<ProofOptions>(ProofFileNames{name}));
        }
        if (read_file(with + ".opb") != read_file(without + ".opb"))
            fail("the inferred constraint changed the OPB");
        for (const auto & name : {with, without})
            dispose_of_proof_files(name);
        println(cerr, "the OPB is untouched");
    }

    // Claiming one better must fail, in both directions, and so must running
    // the arithmetic on a degree that includes a demand the cut is not about.
    // The fixture carries a spare task precisely so the last of those has
    // something to skip.
    {
        auto honest = make_shared<InferredCumulativeStats>();
        solve_instance(lifted_instance_with_spare(13), Setup{.stats = honest}, make_optional("inferred_cumulative_honest"));
        if (honest->non_unit_cuts_posted != 1)
            fail("mutations: the honest run posted " + to_string(honest->non_unit_cuts_posted) +
                " cuts with a coefficient above one, so the mutants are not corrupting the cut this file is about");
        println(cerr, "the honest certificate over the spare-task fixture verifies");

        for (const auto & [what, mutation] :
            {std::pair<string, InferredCumulativeMutation>{"one less capacity", inferred_cumulative_mutation::ClaimTighterCapacity{}},
                std::pair<string, InferredCumulativeMutation>{"one more height", inferred_cumulative_mutation::ClaimTallerTask{}},
                std::pair<string, InferredCumulativeMutation>{"a tighter row", inferred_cumulative_mutation::ClaimTighterRow{}}}) {
            const string name = "inferred_cumulative_mutation";
            Problem p;
            post(p, lifted_instance_with_spare(13), Setup{.mutation = mutation});
            solve_with(
                p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return true; }}, make_optional<ProofOptions>(ProofFileNames{name}));

            if (run_veripb(name + ".opb", name + ".pbp"))
                fail("veripb accepted the " + what + " mutation, so the honest certificate has slack in it");
            println(cerr, "veripb rejected the {} mutation, as expected", what);
            dispose_of_proof_files(name);
        }
    }

    // Two resources, which is what Equation 4's lifting is actually over, and
    // the only fixture here whose certificate carries a row onto flags that are
    // not its own.
    {
        auto stats = make_shared<InferredCumulativeStats>();

        auto resources_only = solve_instance(two_resource_instance(7), Setup{.stage = Stage::none}, nullopt);
        if (resources_only.refuted_at_root)
            fail("two resources: the rows alone refuted at the root, so the fixture proves nothing");

        auto lifted =
            solve_instance(two_resource_instance(7), Setup{.stats = stats}, proofs ? make_optional("inferred_cumulative_two_resources") : nullopt);

        if (stats->donors_seen != 2)
            fail("two resources: saw " + to_string(stats->donors_seen) + " donors, so they were not both offered");
        if (stats->multi_resource_cuts_posted == 0)
            fail("two resources: every posted cut came from a single row, so the crossing this fixture exists for never ran");
        if (stats->non_unit_cuts_posted == 0)
            fail("two resources: nothing posted with a coefficient above one, so this is the capacity-one stage's case and not this one");
        // Fifteen units of a supply of two: eight, which is the optimum, and one
        // more than either row reaches on its own.
        if (stats->largest_capacity_bound != 8_i)
            fail("two resources: reported a makespan bound of " + to_string(stats->largest_capacity_bound.raw_value) +
                ", not the eight the cut "
                "carries");
        if (! lifted.refuted_at_root)
            fail("two resources: the cut did not refute a horizon of seven at the root");

        println(cerr, "two resources: {} cuts posted, {} of them over more than one row, bound {}, refuted at the root against {} nodes without",
            stats->cuts_posted, stats->multi_resource_cuts_posted, stats->largest_capacity_bound.raw_value, resources_only.recursions);
    }

    // And the horizon it does not refute enumerates correctly, which is the
    // half that says the cut is implied rather than merely strong.
    {
        auto stats = make_shared<InferredCumulativeStats>();
        auto instance = two_resource_instance(8);
        auto outcome = solve_instance(instance, Setup{.stats = stats}, proofs ? make_optional("inferred_cumulative_two_resources_sat") : nullopt);
        if (stats->multi_resource_cuts_posted == 0)
            fail("two resources, satisfiable: no cut over more than one row was posted");
        if (outcome.solutions != expected_solutions(instance))
            fail("two resources, satisfiable: " + to_string(outcome.solutions.size()) + " solutions against " +
                to_string(expected_solutions(instance).size()) + " by brute force");
        println(cerr, "two resources: {} solutions at the bound, matching brute force", outcome.solutions.size());
    }

    // Every mutation again, over the fixture that crosses --- including the one
    // that can only exist here, where a row is carried onto the wrong member's
    // flags. With a single donor there is no crossing for it to corrupt.
    if (proofs) {
        for (const auto & [what, mutation] :
            {std::pair<string, InferredCumulativeMutation>{"one less capacity", inferred_cumulative_mutation::ClaimTighterCapacity{}},
                std::pair<string, InferredCumulativeMutation>{"one more height", inferred_cumulative_mutation::ClaimTallerTask{}},
                std::pair<string, InferredCumulativeMutation>{"a tighter row", inferred_cumulative_mutation::ClaimTighterRow{}},
                std::pair<string, InferredCumulativeMutation>{"the wrong task bridged", inferred_cumulative_mutation::BridgeWrongTask{}}}) {
            const string name = "inferred_cumulative_two_resource_mutation";
            Problem p;
            post(p, two_resource_instance(8), Setup{.mutation = mutation});
            solve_with(
                p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return true; }}, make_optional<ProofOptions>(ProofFileNames{name}));

            if (run_veripb(name + ".opb", name + ".pbp"))
                fail("veripb accepted the " + what + " mutation over two resources, so that certificate has slack in it");
            println(cerr, "veripb rejected the {} mutation over two resources, as expected", what);
            dispose_of_proof_files(name);
        }
    }

    // And the markers say the derivation actually ran.
    {
        const string name = "inferred_cumulative_markers";
        solve_instance(lifted_instance(13), Setup{}, make_optional(name), false);
        if (! run_veripb(name + ".opb", name + ".pbp"))
            fail("markers: veripb rejected the proof");
        auto proof = read_file(name + ".pbp");
        if (0 == count_occurrences(proof, "presolve lifted cover: inferred a cut"))
            fail("markers: no cut was recorded as inferred");
        println(cerr, "markers: the inferred cut is recorded in the proof");
        dispose_of_proof_files(name);
    }

    return EXIT_SUCCESS;
}
