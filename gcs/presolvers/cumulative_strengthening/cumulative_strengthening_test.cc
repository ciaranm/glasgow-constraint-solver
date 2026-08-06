/* Schulz's strengthenings, as a presolver over posted Cumulatives.
 *
 * What is hard to test here is not that the proofs verify --- they do that
 * whether the presolver fired or not, since a presolver that declines every
 * donor writes nothing and leaves a perfectly good proof behind. Nor is a
 * solution-equivalence check enough, for the same reason. Worse, the rules are
 * *time-table neutral* by design, so even the search tree is unchanged unless
 * energy reasoning is on. Three separate nets are therefore needed:
 *
 *   - the stats block, asserting the presolver fired, on how many donors, by
 *     how much, on how many raised heights, and down which derivation;
 *   - an energy-rule differential, where the strengthening is the only thing
 *     that refutes at the root;
 *   - mutations, asserting VeriPB rejects a derivation that claims more than it
 *     proved.
 *
 * And the neutrality itself is a tripwire rather than a caveat: under
 * time-tabling alone the node counts must be *identical*. For the capacity that
 * is because a load is a sum of heights and so clears the donor's capacity
 * exactly when it clears kappa. For a *raised* height it is a separate argument
 * --- the profile really is different --- and it holds because a raised task
 * conflicts with everything, so any time-table verdict a raised height reaches
 * is one the donor's own capacity reaches too. A node-count difference would
 * mean one of those two arguments was wrong, which is what an unsound
 * strengthening looks like.
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

    /// An instance whose tasks are optional. Deliberately not folded into
    /// Instance: a solution then carries a presence per task as well as a
    /// start, which every other fixture in this file would have to account for
    /// and none of them cares about.
    struct OptionalInstance
    {
        vector<pair<int, int>> start_ranges;
        vector<int> lengths;
        vector<int> heights;
        /// Per task, the domain its presence variable is declared over.
        vector<pair<int, int>> presence_ranges;
        int capacity;
    };

    /// Over an assignment that is every start followed by every presence, which
    /// is the shape build_expected produces and the shape the solution callback
    /// records.
    auto is_satisfying(const OptionalInstance & inst, const vector<int> & assignment) -> bool
    {
        auto n = inst.start_ranges.size();
        auto start = [&](size_t i) { return assignment[i]; };
        auto present = [&](size_t i) { return assignment[n + i] != 0; };

        int t_lo = INT_MAX, t_hi = INT_MIN;
        for (size_t i = 0; i < n; ++i) {
            if (inst.lengths[i] == 0 || inst.heights[i] == 0 || ! present(i))
                continue;
            t_lo = min(t_lo, start(i));
            t_hi = max(t_hi, start(i) + inst.lengths[i] - 1);
        }
        for (int t = t_lo; t <= t_hi; ++t) {
            int load = 0;
            for (size_t i = 0; i < n; ++i)
                if (present(i) && start(i) <= t && t < start(i) + inst.lengths[i])
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
        long long raise_budget = 5000;
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
            presolver.with_dynamic_programming_budget(setup.budget).with_raise_budget(setup.raise_budget).with_proof_mutation(setup.mutation);
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

    /// Solve an optional instance, collecting the same (starts, presences)
    /// tuples brute force produces.
    auto solve_optional(const OptionalInstance & inst, const shared_ptr<CumulativeStrengtheningStats> & stats, const optional<string> & proof_name)
        -> Outcome
    {
        Problem p;
        vector<IntegerVariableID> starts, presences, lengths, heights;
        for (size_t i = 0; i < inst.start_ranges.size(); ++i) {
            starts.push_back(p.create_integer_variable(Integer{inst.start_ranges[i].first}, Integer{inst.start_ranges[i].second}));
            presences.push_back(p.create_integer_variable(Integer{inst.presence_ranges[i].first}, Integer{inst.presence_ranges[i].second}));
            lengths.push_back(constant_variable(Integer{inst.lengths[i]}));
            heights.push_back(constant_variable(Integer{inst.heights[i]}));
        }

        p.post(Cumulative{starts, lengths, heights, presences, constant_variable(Integer{inst.capacity})});
        if (stats)
            p.add_presolver(CumulativeStrengthening{stats});

        Outcome outcome;
        bool reached_a_node = false, found_a_solution = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               found_a_solution = true;
                               vector<int> solution;
                               for (const auto & v : starts)
                                   solution.push_back(s(v).raw_value);
                               for (const auto & v : presences)
                                   solution.push_back(s(v).raw_value);
                               outcome.solutions.insert(move(solution));
                               return true;
                           },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    return true;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);

        outcome.refuted_at_root = ! reached_a_node && ! found_a_solution;

        if (proof_name)
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

    /// The same discipline for the split: which tasks the presolver will raise
    /// to the capacity, and what kappa the rest of them come to. Asserted as
    /// arithmetic first, because the whole rule turns on the pairwise test and
    /// a fixture that has drifted over the boundary --- `c_i = C - min` rather
    /// than one above it --- is a fixture for the other case entirely.
    ///
    /// Every fixture here has tasks whose windows all overlap, so the overlap
    /// half of the presolver's test is not repeated.
    auto check_split(const string & what, const vector<int> & heights, int capacity, const vector<size_t> & expected_raised, int expected_kappa)
        -> void
    {
        vector<size_t> raised;
        vector<Integer> rest;
        for (size_t i = 0; i < heights.size(); ++i) {
            bool conflicts_with_everything = true;
            for (size_t j = 0; j < heights.size(); ++j)
                if (i != j && heights[i] + heights[j] <= capacity)
                    conflicts_with_everything = false;
            if (conflicts_with_everything)
                raised.push_back(i);
            else
                rest.push_back(Integer{heights[i]});
        }

        auto as_text = [](const vector<size_t> & positions) {
            string text;
            for (auto p : positions)
                text += (text.empty() ? "" : ", ") + std::to_string(p);
            return "{" + text + "}";
        };
        if (raised != expected_raised)
            fail(what + ": the tasks that fill the resource on their own are " + as_text(raised) + ", not the " + as_text(expected_raised) +
                " the fixture claims");

        auto kappa = largest_subset_sum_at_most(rest, Integer{capacity});
        if (kappa != Integer{expected_kappa})
            fail(what + ": kappa over the rest is " + std::to_string(kappa.raw_value) + ", not the " + std::to_string(expected_kappa) +
                " the fixture claims");
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

    // And the split the heights half turns on, checked the same way. The R1
    // sharpness fixture is barely over the line --- five is one above
    // `C - min = 4` --- and its control sits exactly on it, which is the case
    // the rule must *not* fire for.
    check_split("R1 fixture", {5, 4, 2}, 6, {0}, 6);
    check_split("R1 control", {4, 4, 2}, 6, {}, 6);
    check_split("full-task pack fixture", {8, 3, 3, 3, 3, 3}, 8, {0}, 6);
    check_split("knapsack raise fixture", {1, 3, 4, 6}, 6, {3}, 5);
    check_split("gcd pack fixture", {3, 3, 3, 3, 3, 3, 3}, 8, {}, 6);
    check_split("deep gap fixture", {2, 6, 6}, 10, {}, 8);

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
        if (stats->tasks_raised != 0)
            fail("pack fixture: a height was raised, so the fixture is not testing the capacity rule on its own");
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

    // Heights {2, 6, 6} against a capacity of ten: the gcd is two, so Schulz's
    // gcd rule offers ten, but 2 + 6 = 8 is the largest load that can actually
    // be reached, and only the dynamic programming gets there. No task fills
    // the resource on its own --- 2 + 6 fits --- so nothing is raised and this
    // is the capacity rule alone.
    const Instance deep_gap{{{0, 3}, {0, 3}, {0, 3}}, {2, 2, 2}, {2, 6, 6}, 10};

    // Heights {1, 3, 4, 6} against a capacity of six. The six conflicts with
    // everything, so it is raised; kappa over the remaining {1, 3, 4} is five,
    // which the gcd cannot reach. Both halves of the rule, in one fixture, and
    // the raise takes four `pol` steps because {1, 3, 4} overshoots five by
    // three.
    const Instance knapsack_raise{{{0, 3}, {0, 3}, {0, 3}, {0, 3}}, {2, 2, 2, 2}, {1, 3, 4, 6}, 6};

    // Heights {5, 4, 2} against a capacity of six: the issue's R1 fixture,
    // where five is one above `C - min` and is raised to the capacity, and
    // where the capacity itself does not move at all. So the only thing the
    // presolver does here is raise a height.
    const Instance r1{{{0, 3}, {0, 3}, {0, 3}}, {2, 2, 2}, {5, 4, 2}, 6};

    for (const auto & [what, inst] : {pair<string, Instance>{"searchy", searchy}, pair<string, Instance>{"deep gap", deep_gap},
             pair<string, Instance>{"knapsack raise", knapsack_raise}, pair<string, Instance>{"R1", r1}}) {
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
        println(cerr, "{} neutrality: {} nodes either way, capacity down by {}, {} heights raised", what, with.recursions,
            stats->capacity_units_removed.raw_value, stats->tasks_raised);
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
        if (stats->capacity_units_removed != 2_i)
            fail("deep gap fixture: took " + std::to_string(stats->capacity_units_removed.raw_value) + " units off, not the two 10 to 8 is");
        if (stats->tasks_raised != 0)
            fail("deep gap fixture: a height was raised, so the fixture is not testing the capacity rule on its own");
        if (proofs && stats->rows_by_division != 0)
            fail("deep gap fixture: a row took the divisibility path, so the fixture is not testing the knapsack rule");
        if (proofs && stats->rows_by_dynamic_programming == 0)
            fail("deep gap fixture: no row took the dynamic programming path");
        println(cerr, "deep gap fixture: {} rows by dynamic programming", stats->rows_by_dynamic_programming);
    }

    // The heights half, and what it buys. Five unit-length tasks of height
    // three plus one that fills the resource, all able to run in [0, 3),
    // against a capacity of eight.
    //
    // The capacity rule alone gets nothing here: the tall task reaches eight
    // on its own, so the largest reachable load *is* the capacity. Setting it
    // aside takes kappa to six, and its own height comes down to six with it,
    // which is what makes the energy sums come apart --- the window supplies
    // twenty-four at a capacity of eight, covering the twenty-three the tasks
    // need, and eighteen at six against the twenty-one they then need.
    const Instance full_task_pack{{{0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}}, {1, 1, 1, 1, 1, 1}, {8, 3, 3, 3, 3, 3}, 8};

    {
        auto stats = make_shared<CumulativeStrengtheningStats>();

        auto donor_only = solve_it(full_task_pack, Setup{.presolve = false}, nullopt);
        if (donor_only.refuted_at_root)
            fail("full-task pack: the donor alone refuted at the root, so the fixture proves nothing");

        // And the capacity rule on its own does not get there either, which is
        // the claim that makes this a fixture for the heights half rather than
        // another version of the pack one. Checked by arithmetic rather than by
        // a toggle: kappa over *every* task is the capacity, so the presolver
        // that stops at the capacity rule declines the donor outright.
        vector<Integer> every_height{8_i, 3_i, 3_i, 3_i, 3_i, 3_i};
        if (largest_subset_sum_at_most(every_height, 8_i) != 8_i)
            fail("full-task pack: the capacity rule alone would have strengthened this, so the fixture is not about raising");

        auto strengthened =
            solve_it(full_task_pack, Setup{.stats = stats}, proofs ? make_optional("cumulative_strengthening_full_task_pack") : nullopt);
        if (! strengthened.refuted_at_root)
            fail("full-task pack: the strengthened constraint did not refute at the root");
        if (! strengthened.solutions.empty())
            fail("full-task pack: the instance is unsatisfiable but solutions were reported");

        if (stats->tasks_raised != 1)
            fail("full-task pack: raised " + std::to_string(stats->tasks_raised) + " heights, not the one");
        if (stats->capacity_units_removed != 2_i)
            fail(
                "full-task pack: took " + std::to_string(stats->capacity_units_removed.raw_value) + " units off the capacity, not the two 8 to 6 is");
        if (proofs && stats->rows_with_a_raise == 0)
            fail("full-task pack: no row needed at-most-one reasoning, so nothing was raised in the proof");
        println(cerr, "full-task pack: refuted at the root, {} rows raised over {} pol steps", stats->rows_with_a_raise, stats->raise_lines_emitted);
    }

    // The R1 fixture and its control, as the issue states them. Five is one
    // above `C - min = 4` and is raised; four is exactly on it and is not, and
    // since nothing else moves either the whole donor is then declined.
    {
        auto stats = make_shared<CumulativeStrengtheningStats>();
        auto outcome = solve_it(r1, Setup{.stats = stats}, proofs ? make_optional("cumulative_strengthening_r1") : nullopt);

        set<vector<int>> expected;
        build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(r1, starts); }, r1.start_ranges);
        if (expected != outcome.solutions)
            fail("R1 fixture: solutions do not match brute force");
        if (stats->tasks_raised != 1)
            fail("R1 fixture: raised " + std::to_string(stats->tasks_raised) + " heights, not the one");
        if (stats->capacity_units_removed != 0_i)
            fail("R1 fixture: the capacity moved, so the fixture is not testing raising on its own");
        println(cerr, "R1 fixture: one height raised to the capacity, which did not move");
    }

    const Instance r1_control{{{0, 3}, {0, 3}, {0, 3}}, {2, 2, 2}, {4, 4, 2}, 6};

    {
        auto stats = make_shared<CumulativeStrengtheningStats>();
        auto outcome = solve_it(r1_control, Setup{.stats = stats}, proofs ? make_optional("cumulative_strengthening_r1_control") : nullopt);

        if (stats->donors_strengthened != 0)
            fail("R1 control: a task whose height is exactly `C - min` was raised");
        if (stats->declined_nothing_to_gain != 1)
            fail("R1 control: the donor was passed over for the wrong reason");

        set<vector<int>> expected;
        build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(r1_control, starts); }, r1_control.start_ranges);
        if (expected != outcome.solutions)
            fail("R1 control: solutions do not match brute force");
    }

    // Two tasks raised in the same row, which is a different shape again: the
    // second one is raised into the row the first one left behind, so its own
    // at-most-ones have to include the one tying it to a task whose coefficient
    // is already the capacity rather than its posted height.
    const Instance two_full{{{0, 3}, {0, 3}, {0, 3}, {0, 3}}, {2, 2, 2, 2}, {7, 7, 3, 3}, 8};

    {
        auto stats = make_shared<CumulativeStrengtheningStats>();
        auto outcome = solve_it(two_full, Setup{.stats = stats}, proofs ? make_optional("cumulative_strengthening_two_full") : nullopt);

        set<vector<int>> expected;
        build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(two_full, starts); }, two_full.start_ranges);
        if (expected != outcome.solutions)
            fail("two-raised fixture: solutions do not match brute force");
        if (stats->tasks_raised != 2)
            fail("two-raised fixture: raised " + std::to_string(stats->tasks_raised) + " heights, not the two");
        if (stats->capacity_units_removed != 2_i)
            fail("two-raised fixture: took " + std::to_string(stats->capacity_units_removed.raw_value) + " units off the capacity, not the two");
        println(cerr, "two-raised fixture: {} pol steps over {} raised rows", stats->raise_lines_emitted, stats->rows_with_a_raise);
    }

    // Both halves at once, over a raise that takes several steps.
    {
        auto stats = make_shared<CumulativeStrengtheningStats>();
        auto outcome = solve_it(knapsack_raise, Setup{.stats = stats}, proofs ? make_optional("cumulative_strengthening_knapsack_raise") : nullopt);

        set<vector<int>> expected;
        build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(knapsack_raise, starts); }, knapsack_raise.start_ranges);
        if (expected != outcome.solutions)
            fail("knapsack raise fixture: solutions do not match brute force");
        if (stats->tasks_raised != 1 || stats->capacity_units_removed != 1_i)
            fail("knapsack raise fixture: raised " + std::to_string(stats->tasks_raised) + " heights and took " +
                std::to_string(stats->capacity_units_removed.raw_value) + " off the capacity, wanting one of each");
        if (proofs && stats->rows_by_dynamic_programming == 0)
            fail("knapsack raise fixture: no row took the dynamic programming path, so it is not exercising both halves");
        if (proofs && stats->raise_lines_emitted <= stats->rows_with_a_raise)
            fail("knapsack raise fixture: " + std::to_string(stats->raise_lines_emitted) + " pol steps over " +
                std::to_string(stats->rows_with_a_raise) + " rows, so no raise took more than one step");
        println(cerr, "knapsack raise fixture: {} pol steps over {} raised rows", stats->raise_lines_emitted, stats->rows_with_a_raise);
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

    // Optional donors, which are not a restriction: the presence is a conjunct
    // of the activity flag rather than a term beside it, so the rows this
    // presolver argues over are the same shape either way.
    //
    // Two of them, because they exercise different halves. With presences
    // declared over {1, 1} every rule fires exactly where it would with no
    // presences at all --- and every flag still carries a presence conjunct
    // that every reason has to carry too, so this is the fixture that would
    // catch a pin emitted without one. With them over {0, 1} the rules mostly
    // hold off until the search decides a presence, and what is checked is that
    // no solution was lost on the way.
    //
    // Five tasks of height three and length two, over a window four time points
    // wide. Eight units of capacity supply thirty-two there, and the
    // strengthened six supply twenty-four, which is short of the thirty the
    // tasks need --- the energy gap that rounding a capacity by integrality
    // opens up, and one the donor cannot reach for itself. So the refutation
    // below is exclusively the derived constraint's, drawn over the donor's
    // flags, and every activity it pins has to name a presence.
    //
    // The starts span three values rather than two on purpose: a {0, 1} domain
    // is direct-only encoded, and prepare_cumulative_overload_check leaves such
    // a task out of the energy set for want of order literals.
    for (const auto & [what, presence_range] : {pair<string, pair<int, int>>{"present", {1, 1}}, {"undecided", {0, 1}}}) {
        auto stats = make_shared<CumulativeStrengtheningStats>();
        const OptionalInstance inst{
            {{0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}}, {2, 2, 2, 2, 2}, {3, 3, 3, 3, 3}, vector<pair<int, int>>(5, presence_range), 8};

        auto outcome = solve_optional(inst, stats, proofs ? make_optional("cumulative_strengthening_optional_" + what) : nullopt);

        // The donor's heights are all multiples of three and its capacity is
        // not, so the subset sum rounds eight down to six. Assert it: a fixture
        // that quietly stopped strengthening would pass everything else here.
        if (stats->donors_strengthened != 1)
            fail("an optional-task donor was not strengthened, on " + what);
        if (stats->capacity_units_removed != 2_i)
            fail("an optional-task donor was strengthened by the wrong amount, on " + what);

        set<vector<int>> expected;
        auto ranges = inst.start_ranges;
        ranges.insert(ranges.end(), inst.presence_ranges.begin(), inst.presence_ranges.end());
        build_expected(expected, [&](const vector<int> & assignment) { return is_satisfying(inst, assignment); }, ranges);
        if (expected != outcome.solutions)
            fail("optional-task solutions do not match brute force, on " + what);

        // With every task present the energy argument runs at the root and
        // refutes there --- and the donor on its own does not, which is what
        // says the derived constraint did the work rather than merely riding
        // along behind it.
        if (what == "present") {
            if (! outcome.refuted_at_root)
                fail("the strengthened energy check did not refute the all-present instance at the root");
            if (solve_optional(inst, nullptr, nullopt).refuted_at_root)
                fail("the donor alone refuted at the root, so the fixture proves nothing");
        }
    }

    // v1 restrictions, each declined loudly rather than quietly mis-derived.
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

        // And the raising budget, which is a separate knob because it is a
        // separate cost in different units. Zero stops the fixture that raises
        // and leaves the two that do not alone.
        auto raise_stats = make_shared<CumulativeStrengtheningStats>();
        solve_it(knapsack_raise, Setup{.raise_budget = 0, .stats = raise_stats}, make_optional("cumulative_strengthening_budget_raise"));
        if (raise_stats->declined_over_raise_budget != 1)
            fail("a zero raise budget did not stop the raising derivation");

        auto unraised_stats = make_shared<CumulativeStrengtheningStats>();
        solve_it(pack, Setup{.raise_budget = 0, .stats = unraised_stats}, make_optional("cumulative_strengthening_budget_unraised"));
        if (unraised_stats->donors_strengthened != 1)
            fail("a zero raise budget stopped a donor with nothing to raise");
    }

    // Nothing above may have reached the OPB.
    check_opb_unaffected("pack", pack);
    check_opb_unaffected("deep gap", deep_gap);
    check_opb_unaffected("knapsack raise", knapsack_raise);
    check_opb_unaffected("two raised", two_full);
    check_opb_unaffected("full-task pack", full_task_pack);

    // Solution preservation, the defining property of a presolve strengthening.
    // Random instances against brute force, with heights drawn against each
    // instance's own capacity rather than from a fixed pool. Two reasons, both
    // about what the corpus actually covers: a height above the capacity means
    // the donor is declined outright and the instance tests nothing, and a task
    // over half the capacity is what conflicts with everything, so drawing one
    // deliberately is how the heights half gets a turn at all.
    {
        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(2, 4), lo_dist(0, 3), span_dist(0, 3), len_dist(0, 3), cap_dist(4, 12), tall_dist(0, 2);

        // Sixty instances, and then more until the heights half has had a turn.
        // Both assertions below are of the "it actually fired" kind, which is
        // the only sort with any power over a presolver --- doing nothing
        // preserves every solution and verifies every proof --- but a fixed
        // count makes them assertions about the *draw*: seed 268 raises no
        // height in sixty instances, and CI eventually meets such a seed.
        size_t fired = 0, raised = 0;
        int drawn = 0;
        for (; drawn < 240 && (drawn < 60 || 0 == raised || 0 == fired); ++drawn) {
            Instance inst;
            inst.capacity = cap_dist(rand);
            std::uniform_int_distribution<> tall(inst.capacity / 2 + 1, inst.capacity), rest(1, inst.capacity / 2);

            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand), span = span_dist(rand);
                inst.start_ranges.emplace_back(lo, lo + span);
                inst.lengths.push_back(len_dist(rand));
                inst.heights.push_back(0 == tall_dist(rand) ? tall(rand) : rest(rand));
            }

            set<vector<int>> expected;
            build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(inst, starts); }, inst.start_ranges);

            auto stats = make_shared<CumulativeStrengtheningStats>();
            auto outcome = solve_it(inst, Setup{.stats = stats}, nullopt);
            if (outcome.solutions != expected) {
                println(cerr, "starts={} lens={} hts={} c={}", inst.start_ranges, inst.lengths, inst.heights, inst.capacity);
                fail("the strengthening removed solutions");
            }
            fired += stats->donors_strengthened;
            raised += stats->tasks_raised;
        }

        if (fired == 0)
            fail("the presolver fired on none of two hundred and forty random instances, so it checked nothing");
        if (raised == 0)
            fail("no height was raised across two hundred and forty random instances, so the heights half checked nothing");
        println(cerr, "solution preservation: strengthened {} of {} random instances, raising {} heights", fired, drawn, raised);
    }

    if (! proofs) {
        println(cerr, "veripb is not available, so the proof-level checks are skipped");
        return EXIT_SUCCESS;
    }

    // The raise arithmetic has more cases than a fixture set reaches evenly: a
    // raise into a row with nothing else in it, one into a row everything fits
    // alongside, one that takes several steps, and a time point whose own
    // largest load is below the declared capacity and has to be relaxed up to
    // it first. So the corpus gets a second turn with proofs on, where every
    // one of them is checked by veripb rather than by inspection.
    {
        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(2, 4), lo_dist(0, 3), span_dist(0, 3), len_dist(1, 3), cap_dist(4, 10), tall_dist(0, 1);

        // Twenty-five instances, and then more until one of them has had
        // something to raise. About one seed in fifty draws twenty-five that do
        // not, and an assertion failing then would be saying something about the
        // draw rather than about the presolver --- while dropping the assertion
        // would let a sweep that certified no raising at all pass quietly.
        size_t raised = 0, rows = 0;
        for (int k = 0; k < 100 && (k < 25 || 0 == raised); ++k) {
            Instance inst;
            inst.capacity = cap_dist(rand);
            std::uniform_int_distribution<> tall(inst.capacity / 2 + 1, inst.capacity), rest(1, inst.capacity / 2);

            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand), span = span_dist(rand);
                inst.start_ranges.emplace_back(lo, lo + span);
                inst.lengths.push_back(len_dist(rand));
                inst.heights.push_back(0 == tall_dist(rand) ? tall(rand) : rest(rand));
            }

            set<vector<int>> expected;
            build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(inst, starts); }, inst.start_ranges);

            auto stats = make_shared<CumulativeStrengtheningStats>();
            auto outcome = solve_it(inst, Setup{.stats = stats}, make_optional("cumulative_strengthening_sweep"));
            if (outcome.solutions != expected) {
                println(cerr, "starts={} lens={} hts={} c={}", inst.start_ranges, inst.lengths, inst.heights, inst.capacity);
                fail("the verified sweep lost solutions");
            }
            raised += stats->tasks_raised;
            rows += stats->rows_with_a_raise;
        }

        if (raised == 0)
            fail("a hundred swept instances raised nothing, so veripb checked no raising");
        println(cerr, "verified sweep: {} heights raised over {} rows, every proof checked", raised, rows);
    }

    // Mutations. Both corrupt the *conclusion* rather than the route to it,
    // which is what a rule whose content is a numeric bound needs: claiming one
    // better than the largest reachable load, and rounding by a divisor that
    // does not divide every height. The second is worth keeping even though it
    // is a perfectly sound proof step --- it lands on a line that is not the one
    // the derived constraint was told it had, and only the `ia` step pinning
    // each row's content notices that.
    for (const auto & [what, inst, mutation] :
        {std::tuple<string, Instance, CumulativeStrengtheningMutation>{"one better", pack, cumulative_strengthening_mutation::ClaimOneBetter{}},
            std::tuple<string, Instance, CumulativeStrengtheningMutation>{"bogus divisor", pack, cumulative_strengthening_mutation::BogusDivisor{}},
            // The pairwise conflict test is the only thing standing between the
            // heights rule and an unsound constraint, and this is what says so.
            // Run on the control fixture, where the tallest task misses the
            // test by exactly one: raising it anyway claims that a task of
            // height four cannot run beside one of height two under a capacity
            // of six, which it plainly can.
            std::tuple<string, Instance, CumulativeStrengtheningMutation>{
                "unentitled raise", r1_control, cumulative_strengthening_mutation::RaiseUnentitled{}},
            // And the step-size rule, which is the arithmetic a rearrangement
            // of this derivation is most likely to lose: one step too far and
            // the division rounds the degree down instead of up, leaving a
            // sound but weaker line that only the row's own pin objects to.
            std::tuple<string, Instance, CumulativeStrengtheningMutation>{
                "raise too fast", knapsack_raise, cumulative_strengthening_mutation::RaiseTooFast{}}}) {
        const string name = "cumulative_strengthening_mutation";
        solve_it(inst, Setup{.mutation = mutation}, make_optional(name), false);

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
                std::tuple<string, Instance, string, string>{"deep gap", deep_gap, "presolve cumulative kappa", "presolve cumulative gcd"},
                // A raised row is marked as such, and a fixture with nothing to
                // raise must not be: the marker is how a reader tells which of
                // the two rules a row came from.
                std::tuple<string, Instance, string, string>{"knapsack raise", knapsack_raise, "presolve cumulative amo", ""},
                std::tuple<string, Instance, string, string>{"pack, unraised", pack, "presolve cumulative gcd", "presolve cumulative amo"}}) {
            const string name = "cumulative_strengthening_markers";
            // Unverified here, because verifying is what deletes the file this
            // needs to read; veripb still gets its turn, below.
            solve_it(inst, Setup{}, make_optional(name), false);

            auto proof = read_file(name + ".pbp");
            if (! run_veripb(name + ".opb", name + ".pbp"))
                fail(what + " markers: veripb rejected the proof");
            if (0 == count_occurrences(proof, wanted))
                fail(what + " markers: no `" + wanted + "` in the proof, so the rule did not fire where the fixture says");
            if (! unwanted.empty() && 0 != count_occurrences(proof, unwanted))
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
        for (const auto & marker : {"presolve cumulative gcd", "presolve cumulative kappa", "presolve cumulative amo", "presolve cumulative:"})
            if (0 != count_occurrences(proof, marker))
                fail(string{"negative control: `"} + marker + "` in the proof of a donor that was passed over");

        if (read_file(with + ".opb") != read_file(without + ".opb"))
            fail("negative control: the OPB differs from a run with no presolver");

        for (const auto & name : {with, without})
            dispose_of_proof_files(name);
    }

    return EXIT_SUCCESS;
}
