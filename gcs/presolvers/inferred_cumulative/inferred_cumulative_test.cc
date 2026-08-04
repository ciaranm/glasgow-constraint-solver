/* Inferring Cumulative constraints with non-unit heights, by lifting cover
 * inequalities over a posted Cumulative's capacity rows.
 *
 * The fixture that carries this file is one resource of capacity five holding
 * one task of demand five and three of demand two. The cover is the three small
 * ones --- six units into five --- so at most two of them run at once, and the
 * big one lifts into that cover with a coefficient of *two*, since it leaves no
 * room for any of them at all. The result, `2a + b + c + d <= 2`, holds at every
 * occupancy point the row allows and at no rational relaxation of it, and its
 * energy per unit of capacity is ten quarters against the row's eleven fifths.
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
 * over a fixture carrying a spare task, so that the weakening sweep has
 * something to skip as well.
 */

#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
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

    /// One resource: a task list and a capacity, plus the horizon they live in.
    struct Instance
    {
        vector<Integer> demands, lengths;
        Integer capacity;
        int horizon;
    };

    /// The headline fixture. One task of demand five and three of demand two,
    /// all of length four, on a resource of capacity five.
    auto lifted_instance(int horizon) -> Instance
    {
        return Instance{{5_i, 2_i, 2_i, 2_i}, {4_i, 4_i, 4_i, 4_i}, 5_i, horizon};
    }

    /// The same, plus a task the cut does not reach --- short and slight enough
    /// to leave the donor's own energy check with nothing to say --- so that
    /// there is always something in the weakening sweep to skip.
    auto lifted_instance_with_spare(int horizon) -> Instance
    {
        return Instance{{5_i, 2_i, 2_i, 2_i, 1_i}, {4_i, 4_i, 4_i, 4_i, 1_i}, 5_i, horizon};
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
    };

    auto post(Problem & p, const Instance & instance, const Setup & setup) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts;
        for (std::size_t i = 0; i < instance.demands.size(); ++i)
            starts.push_back(p.create_integer_variable(0_i, Integer{instance.horizon} - instance.lengths[i], "s" + to_string(i)));

        p.post(Cumulative{starts, instance.lengths, instance.demands, instance.capacity}.with_rules(setup.rules));

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
        auto ok = [&]() {
            for (int t = 0; t < instance.horizon; ++t) {
                Integer load = 0_i;
                for (std::size_t i = 0; i < n; ++i)
                    if (t >= current[i] && t < current[i] + instance.lengths[i].raw_value)
                        load += instance.demands[i];
                if (load > instance.capacity)
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
            for (int s = 0; s <= instance.horizon - instance.lengths[at].raw_value; ++s) {
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

    // Four tasks of length four into nine time points. The resource supplies
    // forty-five units and the tasks need forty-four, so its own energy check
    // is content; the lifted cut needs twenty units of a supply of eighteen and
    // is not.
    {
        auto stats = make_shared<InferredCumulativeStats>();

        auto donor_only = solve_instance(lifted_instance(9), Setup{.stage = Stage::none}, nullopt);
        if (donor_only.refuted_at_root)
            fail("the donor alone refuted at the root, so the fixture proves nothing");

        auto lifted = solve_instance(lifted_instance(9), Setup{.stats = stats}, proofs ? make_optional("inferred_cumulative_unsat") : nullopt);

        if (stats->cuts_posted != 1)
            fail("posted " + to_string(stats->cuts_posted) + " cuts, not the one the fixture contains");
        if (stats->non_unit_cuts_posted != 1)
            fail("the posted cut had every coefficient at one, so it is not the lifted cut the fixture is about");
        // Sidorov's L: the cut's tasks need 2*4 + 1*4*3 = 20 units of a
        // resource supplying 2 per step, so no schedule can finish before 10.
        if (stats->largest_capacity_bound != 10_i)
            fail("reported a makespan bound of " + to_string(stats->largest_capacity_bound.raw_value) + ", not the ten the cut carries");
        if (stats->lifting_steps == 0)
            fail("no lifting step was taken, so the cut is a plain cover inequality");
        if (! lifted.refuted_at_root)
            fail("the lifted cut did not refute at the root");
        if (! lifted.solutions.empty())
            fail("the instance is unsatisfiable but solutions were reported");

        println(cerr, "lifted cut: refuted at the root against {} nodes without it, bound {}", donor_only.recursions,
            stats->largest_capacity_bound.raw_value);
    }

    // The differential pair. The conflict graph here is a star, so there is no
    // clique of three to find and the capacity-one stage posts nothing --- this
    // instance is closed by a non-unit coefficient or not at all.
    {
        auto stats = make_shared<InferredDisjunctiveStats>();
        auto disjunctive_only = solve_instance(lifted_instance(9), Setup{.stage = Stage::disjunctive, .disjunctive_stats = stats}, nullopt);

        if (stats->conflicting_pairs != 3)
            fail("differential pair: found " + to_string(stats->conflicting_pairs) + " conflicting pairs, not the three of the star");
        if (stats->cliques_posted != 0)
            fail("differential pair: the capacity-one stage posted something, so the comparison is not about lifting");
        if (disjunctive_only.refuted_at_root)
            fail("differential pair: the capacity-one stage refuted at the root, so it did not need this one");
        println(cerr, "differential pair: capacity-one inference finds no clique and does not refute");
    }

    // Twelve time points, where the tasks fit: the big one alone, then two of
    // the small ones, then the last. Still satisfiable, still every solution,
    // and the cut is still posted --- an inferred constraint has to be harmless
    // where it is not decisive.
    {
        auto stats = make_shared<InferredCumulativeStats>();
        auto lifted = solve_instance(lifted_instance(12), Setup{.stats = stats}, proofs ? make_optional("inferred_cumulative_sat") : nullopt);

        if (stats->cuts_posted != 1)
            fail("sharp twin: the cut was not posted, so the comparison is vacuous");
        auto expected = expected_solutions(lifted_instance(12));
        if (expected.empty())
            fail("sharp twin: the fixture has no solutions, so it is not the twin it claims to be");
        if (lifted.solutions != expected)
            fail("sharp twin: solutions do not match brute force, so the cut removed some");
        println(cerr, "sharp twin: {} solutions, matching brute force", lifted.solutions.size());
    }

    // Solution preservation at several shapes, including the spare-task one,
    // where the cut spans some of the resource rather than all of it.
    for (const auto & instance : {lifted_instance(13), lifted_instance_with_spare(11), Instance{{4_i, 4_i, 4_i}, {3_i, 3_i, 3_i}, 10_i, 7}}) {
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

    // Time-table neutrality. A cut is *valid*, so every occupancy point the
    // donor's row allows satisfies it too, and no verdict about a single time
    // point can differ. With the energy rules off everywhere the node counts
    // must be identical.
    {
        const CumulativeRules tt_only{.time_table = true, .overload = false, .profile_overload = false};
        auto stats = make_shared<InferredCumulativeStats>();

        auto without = solve_instance(lifted_instance(12), Setup{.stage = Stage::none, .rules = tt_only}, nullopt);
        auto with = solve_instance(lifted_instance(12), Setup{.rules = tt_only, .inferred_rules = make_optional(tt_only), .stats = stats}, nullopt);

        if (stats->cuts_posted != 1)
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
        auto stats = make_shared<InferredCumulativeStats>();
        solve_instance(lifted_instance(12), Setup{.max_covers = 0, .stats = stats}, nullopt);
        if (stats->cuts_posted != 0)
            fail("a zero cover budget still posted a cut");
        if (stats->covers_considered != 0)
            fail("a zero cover budget grew covers anyway");
        // Nothing posted has to mean no bound claimed: a stale bound would be a
        // lower bound nobody derived.
        if (stats->largest_capacity_bound != 0_i)
            fail("posted no cut but still reported a bound of " + to_string(stats->largest_capacity_bound.raw_value));
    }
    {
        auto stats = make_shared<InferredCumulativeStats>();
        solve_instance(lifted_instance_with_spare(12), Setup{.max_posted = 0, .stats = stats}, nullopt);
        if (stats->cuts_posted != 0)
            fail("a zero output budget still posted a cut");
        if (stats->dropped_over_budget == 0)
            fail("a zero output budget dropped cuts without counting them");
    }
    println(cerr, "budgets: both caps bite, and both are counted");

    // Random instances against brute force, with demands drawn against each
    // instance's own capacity rather than from a fixed pool. A task above half
    // the capacity is the one that lifts into a cover of small tasks with a
    // coefficient above one, so drawing one deliberately is how the non-unit
    // case gets a turn at all --- with a fixed pool it happens by accident and
    // the corpus is seed-flaky about whether it happened.
    {
        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(3, 5), cap_dist(4, 12), len_dist(1, 3), tall_dist(0, 2);

        std::size_t posted = 0, non_unit = 0, steps = 0, weakened = 0;
        for (int k = 0; k < 60; ++k) {
            Instance instance{{}, {}, Integer{cap_dist(rand)}, 0};
            std::uniform_int_distribution<> tall(instance.capacity.raw_value / 2 + 1, static_cast<int>(instance.capacity.raw_value)),
                rest(1, instance.capacity.raw_value / 2);

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

            auto stats = make_shared<InferredCumulativeStats>();
            auto lifted = solve_instance(instance, Setup{.stats = stats}, nullopt);
            if (lifted.solutions != expected_solutions(instance)) {
                println(cerr, "demands={} lengths={} capacity={} horizon={}", instance.demands, instance.lengths, instance.capacity.raw_value,
                    instance.horizon);
                fail("the inferred cut removed solutions");
            }
            posted += stats->cuts_posted;
            non_unit += stats->non_unit_cuts_posted;
            steps += stats->lifting_steps;
            weakened += stats->lifting_steps_weakened;
        }

        if (posted == 0)
            fail("the presolver posted nothing across the random corpus, so it checked nothing");
        if (non_unit == 0)
            fail("no cut in the random corpus had a coefficient above one, so the lifting checked nothing");
        if (steps == 0)
            fail("no lifting step was taken across the random corpus");
        println(cerr,
            "solution preservation: {} cuts over 60 random instances ({} non-unit), {} lifting steps of which {} had to settle for a "
            "smaller coefficient than the knapsack allows",
            posted, non_unit, steps, weakened);
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

    // Nothing may have reached the OPB: the whole plan turns on an inferred
    // constraint being a derivation rather than a model axiom.
    {
        const string with = "inferred_cumulative_opb_with", without = "inferred_cumulative_opb_without";
        for (const auto & [name, stage] : {std::pair{with, Stage::cumulative}, std::pair{without, Stage::none}}) {
            Problem p;
            post(p, lifted_instance(12), Setup{.stage = stage});
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
        solve_instance(lifted_instance_with_spare(11), Setup{.stats = honest}, make_optional("inferred_cumulative_honest"));
        if (honest->cuts_posted != 1 || honest->non_unit_cuts_posted != 1)
            fail("mutations: the honest run posted " + to_string(honest->cuts_posted) + " cuts (" + to_string(honest->non_unit_cuts_posted) +
                " non-unit), so the mutants are not corrupting the cut this file is about");
        println(cerr, "the honest certificate over the spare-task fixture verifies");

        for (const auto & [what, mutation] :
            {std::pair<string, InferredCumulativeMutation>{"one less capacity", inferred_cumulative_mutation::ClaimTighterCapacity{}},
                std::pair<string, InferredCumulativeMutation>{"one more height", inferred_cumulative_mutation::ClaimTallerTask{}},
                std::pair<string, InferredCumulativeMutation>{"a skipped weakening", inferred_cumulative_mutation::SkipAWeakening{}}}) {
            const string name = "inferred_cumulative_mutation";
            Problem p;
            post(p, lifted_instance_with_spare(11), Setup{.mutation = mutation});
            solve_with(
                p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return true; }}, make_optional<ProofOptions>(ProofFileNames{name}));

            if (run_veripb(name + ".opb", name + ".pbp"))
                fail("veripb accepted the " + what + " mutation, so the honest certificate has slack in it");
            println(cerr, "veripb rejected the {} mutation, as expected", what);
            dispose_of_proof_files(name);
        }
    }

    // And the markers say the derivation actually ran.
    {
        const string name = "inferred_cumulative_markers";
        solve_instance(lifted_instance(12), Setup{}, make_optional(name), false);
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
