/* Schulz's capacity strengthenings, as a presolver over posted Cumulatives.
 *
 * What is hard to test here is not that the proofs verify --- they do that
 * whether the presolver fired or not, since a presolver that declines every
 * donor writes nothing and leaves a perfectly good proof behind. Nor is a
 * solution-equivalence check enough, for the same reason. Worse, the rules are
 * *time-table neutral* by design, so even the search tree is unchanged unless
 * energy reasoning is on. Three separate nets are therefore needed:
 *
 *   - the stats block, asserting the presolver fired, on how many donors, by
 *     how much, and down which of the two derivations;
 *   - an energy-rule differential, where the strengthening is the only thing
 *     that refutes at the root;
 *   - mutations, asserting VeriPB rejects a derivation that claims more than it
 *     proved.
 *
 * And the neutrality itself is a tripwire rather than a caveat: under
 * time-tabling alone the node counts must be *identical*, because a load is a
 * sum of heights and so clears the donor's capacity exactly when it clears
 * kappa. A difference would mean the strengthening had changed what the profile
 * permits, which is what an unsound one looks like.
 */

#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/subset_sum_strengthening.hh>
#include <gcs/presolvers/cumulative_strengthening.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <climits>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <numeric>
#include <optional>
#include <random>
#include <set>
#include <string>
#include <tuple>
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
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::shared_ptr;
using std::string;
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
        println(cerr, "cumulative strengthening test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    struct Instance
    {
        vector<pair<int, int>> start_ranges;
        vector<int> lengths;
        vector<int> heights;
        int capacity;
    };

    auto is_satisfying(const Instance & inst, const vector<int> & starts) -> bool
    {
        auto n = inst.start_ranges.size();
        int t_lo = INT_MAX, t_hi = INT_MIN;
        for (size_t i = 0; i < n; ++i) {
            if (inst.lengths[i] == 0 || inst.heights[i] == 0)
                continue;
            t_lo = min(t_lo, starts[i]);
            t_hi = max(t_hi, starts[i] + inst.lengths[i] - 1);
        }
        for (int t = t_lo; t <= t_hi; ++t) {
            int load = 0;
            for (size_t i = 0; i < n; ++i)
                if (starts[i] <= t && t < starts[i] + inst.lengths[i])
                    load += inst.heights[i];
            if (load > inst.capacity)
                return false;
        }
        return true;
    }

    /// How a solve was set up: whether the presolver ran, with which rules on
    /// both sides, and with what corruption.
    struct Setup
    {
        bool presolve = true;
        CumulativeRules rules = CumulativeRules{};
        /// What the derived constraints run. Left alone, the presolver's own
        /// default applies --- energy rules only --- which is what every fixture
        /// but the neutrality one wants, since that default is the thing being
        /// shipped.
        optional<CumulativeRules> derived_rules = nullopt;
        CumulativeStrengtheningMutation mutation = cumulative_strengthening_mutation::None{};
        long long budget = 20000;
        shared_ptr<CumulativeStrengtheningStats> stats = nullptr;
    };

    auto post(Problem & p, const Instance & inst, const Setup & setup) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts;
        for (auto & [lo, hi] : inst.start_ranges)
            starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));

        vector<Integer> lengths, heights;
        for (auto l : inst.lengths)
            lengths.push_back(Integer{l});
        for (auto h : inst.heights)
            heights.push_back(Integer{h});

        p.post(Cumulative{starts, lengths, heights, Integer{inst.capacity}}.with_rules(setup.rules));
        if (setup.presolve) {
            auto presolver = CumulativeStrengthening{setup.stats};
            presolver.with_dynamic_programming_budget(setup.budget).with_proof_mutation(setup.mutation);
            if (setup.derived_rules)
                presolver.with_rules(*setup.derived_rules);
            p.add_presolver(presolver);
        }
        return starts;
    }

    struct Outcome
    {
        set<vector<int>> solutions;
        unsigned long long recursions = 0;
        bool refuted_at_root = false;
    };

    auto solve_it(const Instance & inst, const Setup & setup, const optional<string> & proof_name, bool verify = true) -> Outcome
    {
        Problem p;
        auto starts = post(p, inst, setup);

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

    auto read_file(const string & name) -> string
    {
        ifstream in{name, std::ios::binary};
        if (! in)
            fail("could not read " + name);
        return string{std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
    }

    auto count_occurrences(const string & haystack, const string & needle) -> size_t
    {
        size_t count = 0;
        for (auto at = haystack.find(needle); at != string::npos; at = haystack.find(needle, at + needle.size()))
            ++count;
        return count;
    }

    /// The blanket rule of the whole plan: an inferred constraint is a
    /// derivation, never a model axiom. A presolver that wrote its inference
    /// into the OPB would be changing the statement being verified, and every
    /// proof in this file would verify and mean nothing.
    auto check_opb_unaffected(const string & what, const Instance & inst) -> void
    {
        const string with = "cumulative_strengthening_opb_with", without = "cumulative_strengthening_opb_without";

        auto write_model_only = [&](const string & name, bool presolve) {
            Problem p;
            post(p, inst, Setup{.presolve = presolve});
            solve_with(
                p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, make_optional<ProofOptions>(ProofFileNames{name}));
        };

        write_model_only(with, true);
        write_model_only(without, false);

        if (read_file(with + ".opb") != read_file(without + ".opb"))
            fail("the presolver changed the OPB, on " + what);

        for (const auto & name : {with, without})
            dispose_of_proof_files(name);
    }

    /// Assert the arithmetic against a hand-computed answer before any proof is
    /// involved. If largest_subset_sum_at_most() and the fixture disagree, the
    /// fixture has drifted and every claim built on it is about something else.
    auto check_kappa(const string & what, const vector<int> & heights, int capacity, int expected_kappa, bool expected_by_division) -> void
    {
        vector<Integer> hs;
        for (auto h : heights)
            hs.push_back(Integer{h});

        auto kappa = largest_subset_sum_at_most(hs, Integer{capacity});
        if (kappa != Integer{expected_kappa})
            fail(what + ": kappa is " + std::to_string(kappa.raw_value) + ", not the " + std::to_string(expected_kappa) + " the fixture claims");

        auto divisor = 0_i;
        for (const auto & h : hs)
            divisor = Integer{std::gcd(divisor.raw_value, h.raw_value)};
        auto by_division = (divisor > 1_i && divisor * (Integer{capacity} / divisor) == kappa);
        if (by_division != expected_by_division)
            fail(what + ": the derivation takes the " + (by_division ? "divisibility" : "dynamic programming") +
                " path, not the one the fixture is for");
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);
    auto proofs = can_run_veripb();

    // The sharpness fixtures, checked as arithmetic first.
    //
    // The divisibility one has to be chosen with care, and the obvious candidate
    // is not one: heights {6, 10, 4} against a capacity of 13 have a gcd of two,
    // so Schulz's gcd rule gives 2 * floor(13 / 2) = 12 --- but the largest load
    // those heights can actually reach at or below 13 is 4 + 6 = 10, so the
    // strengthening is to ten and it is the dynamic programming that gets there.
    // Rounding by the gcd is only the whole answer when the gcd's multiples are
    // all reachable, which {2, 4, 6} manages and {6, 10, 4} does not.
    check_kappa("gcd fixture", {2, 4, 6}, 13, 12, true);
    check_kappa("deep gap fixture", {6, 10, 4}, 13, 10, false);
    check_kappa("nothing to gain fixture", {1, 2, 4}, 7, 7, false);

    // The deep gap this rule is famous for --- heights {6, 10, 15} against a
    // capacity of 14, where the overall gcd is one so no rounding reaches the
    // answer of ten --- is a subset-sum fixture and cannot be a Cumulative one:
    // a task of height fifteen under a capacity of fourteen can never run, so
    // the constraint is infeasible before any strengthening is considered. The
    // arithmetic is still worth pinning here, since it is what the instance
    // below is a viable version of.
    check_kappa("deep gap, as arithmetic", {6, 10, 15}, 14, 10, false);

    // The value demonstration. Seven unit-length tasks of height three, all
    // able to run in [0, 3), against a capacity of eight. Every load is a
    // multiple of three, so the capacity is really six --- and that is invisible
    // to time-tabling, since a load clears eight exactly when it clears six. It
    // shows up in the energy argument, where the window [0, 3) supplies capacity
    // times width: twenty-four at a capacity of eight, which covers the twenty-
    // one units the tasks need, and eighteen at six, which does not.
    const Instance pack{{{0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}}, {1, 1, 1, 1, 1, 1, 1}, {3, 3, 3, 3, 3, 3, 3}, 8};

    {
        auto stats = make_shared<CumulativeStrengtheningStats>();

        auto donor_only = solve_it(pack, Setup{.presolve = false}, nullopt);
        if (donor_only.refuted_at_root)
            fail("pack fixture: the donor alone refuted at the root, so the fixture proves nothing");

        auto strengthened = solve_it(pack, Setup{.stats = stats}, proofs ? make_optional("cumulative_strengthening_pack") : nullopt);
        if (! strengthened.refuted_at_root)
            fail("pack fixture: the strengthened constraint did not refute at the root");
        if (! strengthened.solutions.empty())
            fail("pack fixture: the instance is unsatisfiable but solutions were reported");

        if (stats->donors_strengthened != 1)
            fail("pack fixture: strengthened " + std::to_string(stats->donors_strengthened) + " donors, not one");
        if (stats->capacity_units_removed != 2_i)
            fail("pack fixture: took " + std::to_string(stats->capacity_units_removed.raw_value) + " units off the capacity, not the two 8 to 6 is");
        if (proofs && stats->rows_by_dynamic_programming != 0)
            fail("pack fixture: a row took the dynamic programming path, so the fixture is not testing the gcd rule");
        if (proofs && stats->rows_by_division == 0)
            fail("pack fixture: no row took the divisibility path");
        println(cerr, "pack fixture: refuted at the root, {} rows by division", stats->rows_by_division);
    }

    // Time-table neutrality, the tripwire. With the energy rules off on both the
    // donor and the derived constraint, the strengthening must be invisible: the
    // same solutions over exactly the same number of nodes. Anything else means
    // it changed what the profile permits.
    //
    // The derived constraint's rules have to be set explicitly here, and to
    // time-tabling: the presolver ships with time-tabling *off*, on the strength
    // of this very theorem, so leaving the default in place would compare a
    // donor against a donor plus a propagator that does nothing, and kappa would
    // never be used for anything.
    const CumulativeRules tt_only{.time_table = true, .overload = false, .profile_overload = false};

    const Instance searchy{{{0, 5}, {0, 5}, {0, 5}, {0, 5}}, {2, 2, 3, 3}, {2, 2, 2, 4}, 7};

    // Heights {6, 10, 4} against a capacity of thirteen: the gcd is two, so
    // Schulz's gcd rule offers twelve, but 4 + 6 = 10 is the largest load that
    // can actually be reached, and only the dynamic programming gets there.
    const Instance deep_gap{{{0, 3}, {0, 3}, {0, 3}}, {2, 2, 2}, {6, 10, 4}, 13};

    for (const auto & [what, inst] : {pair<string, Instance>{"searchy", searchy}, pair<string, Instance>{"deep gap", deep_gap}}) {
        auto stats = make_shared<CumulativeStrengtheningStats>();

        auto without = solve_it(inst, Setup{.presolve = false, .rules = tt_only}, nullopt);
        auto with = solve_it(inst, Setup{.rules = tt_only, .derived_rules = make_optional(tt_only), .stats = stats}, nullopt);

        if (stats->donors_strengthened != 1)
            fail(what + " neutrality: the presolver did not fire, so the comparison is vacuous");
        if (without.solutions != with.solutions)
            fail(what + " neutrality: the solution set changed");
        if (without.recursions != with.recursions)
            fail(what + " neutrality: " + std::to_string(with.recursions) + " nodes against " + std::to_string(without.recursions) +
                " --- the strengthening is not time-table neutral, which means it is not sound");
        println(cerr, "{} neutrality: {} nodes either way, capacity down by {}", what, with.recursions, stats->capacity_units_removed.raw_value);
    }

    // The deep-gap fixture is the one that exercises the dynamic programming.
    {
        auto stats = make_shared<CumulativeStrengtheningStats>();
        auto outcome = solve_it(deep_gap, Setup{.stats = stats}, proofs ? make_optional("cumulative_strengthening_deep_gap") : nullopt);

        set<vector<int>> expected;
        build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(deep_gap, starts); }, deep_gap.start_ranges);
        if (expected != outcome.solutions)
            fail("deep gap fixture: solutions do not match brute force");
        // Doubles as the backtracking soak: the derived rows are emitted once,
        // at the top of the proof, and cited at every node. A search that never
        // backtracked would not notice if they had landed at any other level.
        if (outcome.recursions < 5)
            fail("deep gap fixture: the instance did not search, so it soaked nothing");
        if (stats->capacity_units_removed != 3_i)
            fail("deep gap fixture: took " + std::to_string(stats->capacity_units_removed.raw_value) + " units off, not the three 13 to 10 is");
        if (proofs && stats->rows_by_division != 0)
            fail("deep gap fixture: a row took the divisibility path, so the fixture is not testing the knapsack rule");
        if (proofs && stats->rows_by_dynamic_programming == 0)
            fail("deep gap fixture: no row took the dynamic programming path");
        println(cerr, "deep gap fixture: {} rows by dynamic programming", stats->rows_by_dynamic_programming);
    }

    // The negative control. A capacity the heights can reach exactly is already
    // the largest reachable load, so there is nothing to strengthen and nothing
    // may be posted --- and, since a declined donor writes no comment, the OPB
    // and the proof both come out as they would with no presolver at all.
    const Instance nothing_to_gain{{{0, 3}, {0, 3}, {0, 3}}, {2, 2, 2}, {1, 2, 4}, 7};

    {
        auto stats = make_shared<CumulativeStrengtheningStats>();
        auto outcome = solve_it(nothing_to_gain, Setup{.stats = stats}, proofs ? make_optional("cumulative_strengthening_control") : nullopt);

        if (stats->donors_seen != 1)
            fail("negative control: the presolver did not see the donor at all");
        if (stats->donors_strengthened != 0)
            fail("negative control: the presolver strengthened a capacity that was already the largest reachable load");
        if (stats->declined_nothing_to_gain != 1)
            fail("negative control: the donor was passed over for the wrong reason");

        set<vector<int>> expected;
        build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(nothing_to_gain, starts); }, nothing_to_gain.start_ranges);
        if (expected != outcome.solutions)
            fail("negative control: solutions do not match brute force");
    }

    // v1 restrictions, each declined loudly rather than quietly mis-derived.
    {
        auto stats = make_shared<CumulativeStrengtheningStats>();

        Problem p;
        vector<IntegerVariableID> starts, presences;
        for (int i = 0; i < 3; ++i) {
            starts.push_back(p.create_integer_variable(0_i, 3_i));
            presences.push_back(p.create_integer_variable(0_i, 1_i));
        }
        vector<IntegerVariableID> lengths{constant_variable(2_i), constant_variable(2_i), constant_variable(2_i)},
            heights{constant_variable(6_i), constant_variable(10_i), constant_variable(15_i)};
        p.post(Cumulative{starts, lengths, heights, presences, constant_variable(14_i)});
        p.add_presolver(CumulativeStrengthening{stats});
        solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, nullopt);

        if (stats->declined_optional != 1)
            fail("an optional-task donor was not declined");
        if (stats->donors_strengthened != 0)
            fail("an optional-task donor was strengthened anyway");
    }

    {
        auto stats = make_shared<CumulativeStrengtheningStats>();

        Problem p;
        vector<IntegerVariableID> starts;
        for (int i = 0; i < 3; ++i)
            starts.push_back(p.create_integer_variable(0_i, 3_i));
        auto varying_height = p.create_integer_variable(1_i, 6_i);
        vector<IntegerVariableID> lengths{constant_variable(2_i), constant_variable(2_i), constant_variable(2_i)},
            heights{varying_height, constant_variable(10_i), constant_variable(15_i)};
        p.post(Cumulative{starts, lengths, heights, constant_variable(14_i)});
        p.add_presolver(CumulativeStrengthening{stats});
        solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, nullopt);

        if (stats->declined_variable_arguments != 1)
            fail("a variable-height donor was not declined");
        if (stats->donors_strengthened != 0)
            fail("a variable-height donor was strengthened anyway");
    }

    // The budget. Set to zero, the dynamic programming path is unaffordable and
    // its donor is passed over --- while the divisibility path, which is two pol
    // steps and not budgeted, keeps working. This is also the check that the
    // budget is predicted from the same test the derivation applies: if the
    // prediction disagreed, the pack fixture would be declined too.
    if (proofs) {
        auto gap_stats = make_shared<CumulativeStrengtheningStats>();
        solve_it(deep_gap, Setup{.budget = 0, .stats = gap_stats}, make_optional("cumulative_strengthening_budget_gap"));
        if (gap_stats->declined_over_budget != 1)
            fail("a zero budget did not stop the dynamic programming derivation");

        auto pack_stats = make_shared<CumulativeStrengtheningStats>();
        solve_it(pack, Setup{.budget = 0, .stats = pack_stats}, make_optional("cumulative_strengthening_budget_pack"));
        if (pack_stats->donors_strengthened != 1)
            fail("a zero budget stopped the divisibility derivation, which it does not pay for");
    }

    // Nothing above may have reached the OPB.
    check_opb_unaffected("pack", pack);
    check_opb_unaffected("deep gap", deep_gap);

    // Solution preservation, the defining property of a presolve strengthening.
    // Random instances against brute force, with heights drawn so that both
    // derivations get a turn.
    {
        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(2, 4), lo_dist(0, 3), span_dist(0, 3), len_dist(0, 3), cap_dist(2, 12);
        const vector<int> height_pool{1, 2, 3, 4, 5, 6, 10, 15};
        std::uniform_int_distribution<> height_dist(0, static_cast<int>(height_pool.size()) - 1);

        size_t fired = 0;
        for (int k = 0; k < 60; ++k) {
            Instance inst;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand), span = span_dist(rand);
                inst.start_ranges.emplace_back(lo, lo + span);
                inst.lengths.push_back(len_dist(rand));
                inst.heights.push_back(height_pool[height_dist(rand)]);
            }
            inst.capacity = cap_dist(rand);

            set<vector<int>> expected;
            build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(inst, starts); }, inst.start_ranges);

            auto stats = make_shared<CumulativeStrengtheningStats>();
            auto outcome = solve_it(inst, Setup{.stats = stats}, nullopt);
            if (outcome.solutions != expected) {
                println(cerr, "starts={} lens={} hts={} c={}", inst.start_ranges, inst.lengths, inst.heights, inst.capacity);
                fail("the strengthening removed solutions");
            }
            fired += stats->donors_strengthened;
        }

        if (fired == 0)
            fail("the presolver fired on none of the random corpus, so it checked nothing");
        println(cerr, "solution preservation: strengthened {} of 60 random instances", fired);
    }

    if (! proofs) {
        println(cerr, "veripb is not available, so the proof-level checks are skipped");
        return EXIT_SUCCESS;
    }

    // Mutations. Both corrupt the *conclusion* rather than the route to it,
    // which is what a rule whose content is a numeric bound needs: claiming one
    // better than the largest reachable load, and rounding by a divisor that
    // does not divide every height. The second is worth keeping even though it
    // is a perfectly sound proof step --- it lands on a line that is not the one
    // the derived constraint was told it had, and only the `ia` step pinning
    // each row's content notices that.
    for (const auto & [what, mutation] :
        {pair<string, CumulativeStrengtheningMutation>{"one better", cumulative_strengthening_mutation::ClaimOneBetter{}},
            pair<string, CumulativeStrengtheningMutation>{"bogus divisor", cumulative_strengthening_mutation::BogusDivisor{}}}) {
        const string name = "cumulative_strengthening_mutation";
        solve_it(pack, Setup{.mutation = mutation}, make_optional(name), false);

        if (run_veripb(name + ".opb", name + ".pbp"))
            fail("veripb accepted the " + what + " mutation");
        println(cerr, "veripb rejected the {} mutation, as expected", what);
        dispose_of_proof_files(name);
    }

    // The markers, counted. The pack fixture takes the divisibility path at
    // every time point and the deep-gap one the dynamic programming path at
    // every time point, so each fixture must show one marker and not the other.
    {
        for (const auto & [what, inst, wanted, unwanted] :
            {std::tuple<string, Instance, string, string>{"pack", pack, "presolve cumulative gcd", "presolve cumulative kappa"},
                std::tuple<string, Instance, string, string>{"deep gap", deep_gap, "presolve cumulative kappa", "presolve cumulative gcd"}}) {
            const string name = "cumulative_strengthening_markers";
            // Unverified here, because verifying is what deletes the file this
            // needs to read; veripb still gets its turn, below.
            solve_it(inst, Setup{}, make_optional(name), false);

            auto proof = read_file(name + ".pbp");
            if (! run_veripb(name + ".opb", name + ".pbp"))
                fail(what + " markers: veripb rejected the proof");
            if (0 == count_occurrences(proof, wanted))
                fail(what + " markers: no `" + wanted + "` in the proof, so the rule did not fire where the fixture says");
            if (0 != count_occurrences(proof, unwanted))
                fail(what + " markers: `" + unwanted + "` in the proof, so the fixture is exercising the other derivation");
            println(cerr, "{} markers: {} occurrences of `{}`", what, count_occurrences(proof, wanted), wanted);
            dispose_of_proof_files(name);
        }
    }

    // A declined donor writes nothing at all, so its proof is the one a run with
    // no presolver produces.
    {
        const string with = "cumulative_strengthening_control_with", without = "cumulative_strengthening_control_without";
        solve_it(nothing_to_gain, Setup{}, make_optional(with), false);
        solve_it(nothing_to_gain, Setup{.presolve = false}, make_optional(without), false);
        if (! run_veripb(with + ".opb", with + ".pbp"))
            fail("negative control: veripb rejected the proof");

        auto proof = read_file(with + ".pbp");
        for (const auto & marker : {"presolve cumulative gcd", "presolve cumulative kappa", "presolve cumulative:"})
            if (0 != count_occurrences(proof, marker))
                fail(string{"negative control: `"} + marker + "` in the proof of a donor that was passed over");

        if (read_file(with + ".opb") != read_file(without + ".opb"))
            fail("negative control: the OPB differs from a run with no presolver");

        for (const auto & name : {with, without})
            dispose_of_proof_files(name);
    }

    return EXIT_SUCCESS;
}
