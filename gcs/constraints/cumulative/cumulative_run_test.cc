#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/innards/cumulative_mutations.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <climits>
#include <cstdlib>
#include <fstream>
#include <iostream>
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
using std::flush;
using std::getline;
using std::ifstream;
using std::make_optional;
using std::max;
using std::min;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::uniform_int_distribution;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

// Time-table run steps (#1237): a bound push whose chain rules out a whole run
// of start values in one step, against the pushed task's own start-checkpoint
// row, rather than one blocked time point per step. Before them, a short task
// pushed a long way wrote a certificate linear in the distance.

namespace
{
    // The comment a run step writes, which tests count: a step that is never
    // taken makes every other assertion about it vacuous.
    const string run_marker = "cumulative run:";

    // Every size is a range, `{v, v}` being a constant. A presence of `{1, 1}`
    // is a task with no presence variable at all; an instance where every task
    // has one is posted without presences. With `views`, each start is posted
    // as a view one above a variable, which run steps do not speak about.
    struct Instance
    {
        vector<pair<int, int>> starts, lengths, heights, presences;
        pair<int, int> capacity;
        bool views = false;
        // Post a presence of `{1, 1}` as a variable fixed to 1 rather than as
        // no presence at all, so that the task's own term on its checkpoint
        // row is a flag.
        bool presence_variables = false;
    };

    auto is_var(const pair<int, int> & r) -> bool
    {
        return r.first != r.second;
    }

    auto has_presences(const Instance & inst) -> bool
    {
        for (const auto & p : inst.presences)
            if (p != pair{1, 1})
                return true;
        return false;
    }

    // Every variable an assignment fixes, in the order the solutions carry
    // them: starts, then variable lengths, heights and presences, each in task
    // order, and last the capacity if it is a variable.
    auto all_ranges(const Instance & inst) -> vector<pair<int, int>>
    {
        auto ranges = inst.starts;
        for (const auto * family : {&inst.lengths, &inst.heights, &inst.presences})
            for (const auto & r : *family)
                if (is_var(r))
                    ranges.push_back(r);
        if (is_var(inst.capacity))
            ranges.push_back(inst.capacity);
        return ranges;
    }

    auto is_satisfying(const Instance & inst, const vector<int> & vals) -> bool
    {
        auto n = inst.starts.size();
        size_t k = n;
        auto read = [&](const vector<pair<int, int>> & family) {
            vector<int> result(n);
            for (size_t i = 0; i < n; ++i)
                result[i] = is_var(family[i]) ? vals.at(k++) : family[i].first;
            return result;
        };
        auto l = read(inst.lengths), h = read(inst.heights), present = read(inst.presences);
        auto capacity = is_var(inst.capacity) ? vals.at(k++) : inst.capacity.first;

        int t_lo = INT_MAX, t_hi = INT_MIN;
        for (size_t i = 0; i < n; ++i) {
            t_lo = min(t_lo, vals[i]);
            t_hi = max(t_hi, vals[i] + l[i] - 1);
        }
        for (int t = t_lo; t <= t_hi; ++t) {
            int load = 0;
            for (size_t i = 0; i < n; ++i)
                if (present[i] && vals[i] <= t && t < vals[i] + l[i])
                    load += h[i];
            if (load > capacity)
                return false;
        }
        return true;
    }

    struct Posted
    {
        vector<IntegerVariableID> starts, presences, all_vars;
    };

    auto post(Problem & p, const Instance & inst, CumulativeRules rules, CumulativeProofMutation mutation = cumulative_proof_mutation::None{})
        -> Posted
    {
        Posted posted;
        auto make = [&](const pair<int, int> & r, const string & name) -> IntegerVariableID {
            if (! is_var(r))
                return constant_variable(Integer{r.first});
            return p.create_integer_variable(Integer{r.first}, Integer{r.second}, name);
        };
        vector<IntegerVariableID> lengths, heights;
        for (size_t i = 0; i < inst.starts.size(); ++i) {
            auto name = "start" + std::to_string(i);
            if (inst.views)
                posted.starts.push_back(p.create_integer_variable(Integer{inst.starts[i].first - 1}, Integer{inst.starts[i].second - 1}, name) + 1_i);
            else
                posted.starts.push_back(p.create_integer_variable(Integer{inst.starts[i].first}, Integer{inst.starts[i].second}, name));
        }
        posted.all_vars = posted.starts;
        for (size_t i = 0; i < inst.lengths.size(); ++i) {
            lengths.push_back(make(inst.lengths[i], "length" + std::to_string(i)));
            if (is_var(inst.lengths[i]))
                posted.all_vars.push_back(lengths.back());
        }
        for (size_t i = 0; i < inst.heights.size(); ++i) {
            heights.push_back(make(inst.heights[i], "height" + std::to_string(i)));
            if (is_var(inst.heights[i]))
                posted.all_vars.push_back(heights.back());
        }
        for (size_t i = 0; i < inst.presences.size(); ++i) {
            if (inst.presence_variables && ! is_var(inst.presences[i]))
                posted.presences.push_back(
                    p.create_integer_variable(Integer{inst.presences[i].first}, Integer{inst.presences[i].first}, "present" + std::to_string(i)));
            else
                posted.presences.push_back(make(inst.presences[i], "present" + std::to_string(i)));
            if (is_var(inst.presences[i]))
                posted.all_vars.push_back(posted.presences.back());
        }
        auto capacity = make(inst.capacity, "capacity");
        if (is_var(inst.capacity))
            posted.all_vars.push_back(capacity);

        auto cumulative = has_presences(inst) ? Cumulative{posted.starts, lengths, heights, posted.presences, capacity}
                                              : Cumulative{posted.starts, lengths, heights, capacity};
        p.post(cumulative.with_rules(rules).with_proof_mutation(mutation));
        return posted;
    }

    [[nodiscard]] auto count_in_proof(const string & proof_name, const string & needle) -> int
    {
        ifstream f{proof_name + ".pbp"};
        if (! f) {
            println(cerr, "could not open {}.pbp to count markers", proof_name);
            return -1;
        }
        int count = 0;
        for (string line; getline(f, line);)
            if (line.find(needle) != string::npos)
                ++count;
        return count;
    }

    [[nodiscard]] auto count_lines(const string & proof_name) -> int
    {
        return count_in_proof(proof_name, "");
    }

    auto fail(const string & message) -> void
    {
        println(cerr, "cumulative run: {}", message);
        exit(EXIT_FAILURE);
    }

    /// What one task's start and presence are left with once root
    /// propagation has run, or nullopt if the root failed.
    struct RootState
    {
        int start_lb, start_ub, presence_ub;
    };

    auto root_state(const Instance & inst, size_t task, CumulativeRules rules, CumulativeProofMutation mutation, const optional<string> & proof_name)
        -> optional<RootState>
    {
        Problem p;
        auto posted = post(p, inst, rules, mutation);

        optional<RootState> result;
        auto record = [&](const CurrentState & s) {
            if (! result)
                result = RootState{static_cast<int>(s.lower_bound(posted.starts[task]).raw_value),
                    static_cast<int>(s.upper_bound(posted.starts[task]).raw_value),
                    static_cast<int>(s.upper_bound(posted.presences[task]).raw_value)};
            return false;
        };
        solve_with(
            p, SolveCallbacks{.solution = record, .trace = record}, proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        return result;
    }

    /// Exactly the brute-force solutions, with or without a proof, and the
    /// number of run steps taken doing it (-1 without a proof).
    auto check_enumeration(const string & what, const Instance & inst, const optional<string> & proof_name) -> int
    {
        print(cerr, "cumulative run {} starts={} lens={} hts={} pres={} cap={}{}{}", what, inst.starts, inst.lengths, inst.heights, inst.presences,
            inst.capacity, inst.views ? " views" : "", proof_name ? " with proofs:" : ":");
        cerr << flush;

        set<vector<int>> expected, actual;
        build_expected(expected, [&](const vector<int> & vals) { return is_satisfying(inst, vals); }, all_ranges(inst));
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto all_vars = post(p, inst, CumulativeRules{}).all_vars;
        solve_for_tests(p, proof_name, actual, tuple{all_vars});
        auto runs = proof_name ? count_in_proof(*proof_name, run_marker) : -1;
        check_results(proof_name, expected, actual);
        return runs;
    }

    // How far the time points reach, which is what the recovering arm's
    // differential pays for before search.
    auto horizon_of(const Instance & inst) -> int
    {
        int result = 0;
        for (size_t i = 0; i < inst.starts.size(); ++i)
            result = max(result, inst.starts[i].second + inst.lengths[i].second);
        return result;
    }

    auto size_of(const Instance & inst) -> long long
    {
        long long size = 1;
        for (const auto & r : all_ranges(inst))
            size *= r.second - r.first + 1;
        return size;
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto proofs = can_run_veripb();
    // Run steps cite start-checkpoint rows, which the time-indexed arm does not
    // write, and the recovering arm checks every per-time row once before
    // search, which is a proof as long as the horizon whatever the chains do.
    // The counts are the shipped encoding's, and the other arms leave out the
    // wide fixtures, whose whole point is a horizon too long to pay for.
    const auto * encoding = std::getenv("GCS_CUMULATIVE_ENCODING");
    auto shipped = ! encoding || ! *encoding || string{encoding} == "start-checkpoint";
    const CumulativeRules without{.time_table = false};
    const CumulativeRules with{};

    auto plain = [](vector<pair<int, int>> starts, vector<pair<int, int>> lengths, vector<pair<int, int>> heights, pair<int, int> capacity) {
        return Instance{starts, lengths, heights, vector<pair<int, int>>(starts.size(), {1, 1}), capacity};
    };

    // The issue's instance: one task fixed over [0, 5000) on a resource of
    // capacity one, and a task of length one that could start anywhere in
    // [0, 10000]. One push takes it to 5000, which was a chain of 5000 steps
    // and about 150,000 proof lines, and is one run step now.
    const auto long_push = plain({{0, 0}, {0, 10000}}, {{5000, 5000}, {1, 1}}, {{1, 1}, {1, 1}}, {1, 1});

    // Its mirror: the fixed task is at the top, so the push is downwards.
    const auto long_push_down = plain({{5001, 5001}, {0, 10000}}, {{5000, 5000}, {1, 1}}, {{1, 1}, {1, 1}}, {1, 1});

    // A staircase of fixed tasks: [0, 3) at height 2, [3, 6) at 2, and two of
    // height 1 over [6, 8) and [6, 9), so a task of height 1 cannot start
    // before 8 on capacity 2. Three runs, each citing different tasks, the
    // last citing two of them together and running only as far as the one
    // that finishes first.
    const auto stairs_tasks = vector<pair<int, int>>{{0, 0}, {3, 3}, {6, 6}, {6, 6}};
    auto stairs = [&](pair<int, int> length) {
        auto starts = stairs_tasks, lengths = vector<pair<int, int>>{{3, 3}, {3, 3}, {2, 2}, {3, 3}};
        auto heights = vector<pair<int, int>>{{2, 2}, {2, 2}, {1, 1}, {1, 1}, {1, 1}};
        starts.emplace_back(0, 30);
        lengths.push_back(length);
        return plain(starts, lengths, heights, {2, 2});
    };
    // A task of length 5 against a short plateau over [0, 3) and a long one
    // over [3, 30). From 0 a time-point step reaches further than a run does,
    // to 5, and from there a run reaches 30, so the chain takes both kinds.
    const auto stairs_long = plain({{0, 0}, {3, 3}, {0, 60}}, {{3, 3}, {27, 27}, {5, 5}}, {{2, 2}, {2, 2}, {1, 1}}, {2, 2});

    // A task that could start anywhere in [0, 5] and fits nowhere beside a
    // fixed one over [0, 6), so it is absent: presence falsification, whose
    // chain takes run steps as a push does.
    const auto falsify = Instance{{{0, 0}, {0, 5}}, {{6, 6}, {1, 1}}, {{1, 1}, {1, 1}}, {{1, 1}, {0, 1}}, {1, 1}};

    // A present task in a constraint with presences, whose own term on its
    // checkpoint row is then a flag, and a pushed task whose length is a
    // variable, whose term is a flag for that reason; the fixed task's length
    // is a variable too.
    const auto present =
        Instance{{{0, 0}, {0, 20}, {30, 30}}, {{10, 10}, {1, 1}, {1, 1}}, {{1, 1}, {1, 1}, {1, 1}}, {{1, 1}, {1, 1}, {0, 1}}, {1, 1}, false, true};
    const auto var_length = plain({{0, 0}, {0, 20}}, {{10, 12}, {1, 3}}, {{1, 1}, {1, 1}}, {1, 1});

    // The capacity is a variable, counted at the most it can be.
    const auto var_capacity = plain({{0, 0}, {0, 20}}, {{10, 10}, {1, 1}}, {{2, 2}, {1, 1}}, {1, 2});

    // Run steps only cite tasks whose pins they know how to write. Not here: a
    // pushed task of variable height, and starts that are views. Both still
    // push, through per-time steps.
    const auto var_height = plain({{0, 0}, {0, 20}}, {{10, 10}, {1, 1}}, {{1, 1}, {1, 3}}, {1, 1});
    const auto views = Instance{{{0, 0}, {0, 100}}, {{50, 50}, {1, 1}}, {{1, 1}, {1, 1}}, {{1, 1}, {1, 1}}, {1, 1}, true};

    // The task the run cites still has a start range here, so its pair flags
    // are not settled by unit propagation over its bits the way a fixed
    // task's are. On long_push, dropping the only cited task verifies: the
    // model closes the push without the pin.
    const auto mutation_fixture = plain({{0, 2}, {2, 30}}, {{10, 10}, {1, 1}}, {{1, 1}, {1, 1}}, {1, 1});

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<CumulativeProofMutation> mutation;
        string proof_basename = "cumulative_run_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=toofar")
                mutation = cumulative_proof_mutation::RunOneTooFar{};
            else if (arg == "--mutate=drop")
                mutation = cumulative_proof_mutation::DropRunContributor{};
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            if (! root_state(mutation_fixture, 1, with, *mutation, make_optional(proof_basename)))
                fail("mutation mode: nothing was reached, so the proof is empty");
            if (count_in_proof(proof_basename, run_marker) == 0)
                fail("mutation mode: no run step was taken, so there was nothing to corrupt");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // The pushes land where the profile says, the same with a proof as
    // without, and only time-tabling makes them. `runs` is how many run steps
    // the proof should take; `max_lines` bounds the whole proof, which is the
    // point of the exercise.
    struct Expected
    {
        string name;
        Instance inst;
        size_t task;
        int start_lb, start_ub, presence_ub, runs, max_lines;
    };
    for (const auto & e :
        vector<Expected>{{"long_push", long_push, 1, 5000, 10000, 1, 1, 200}, {"long_push_down", long_push_down, 1, 0, 5000, 1, 1, 200},
            {"stairs", stairs({1, 1}), 4, 8, 30, 1, 3, 400}, {"stairs_long", stairs_long, 2, 30, 60, 1, 1, 400},
            {"falsify", falsify, 1, 0, 5, 0, 1, 200}, {"present", present, 1, 10, 20, 1, 1, 200}, {"var_length", var_length, 1, 10, 20, 1, 1, 200},
            {"var_capacity", var_capacity, 1, 10, 20, 1, 1, 200}, {"var_height", var_height, 1, 10, 20, 1, 0, 5000},
            {"views", views, 1, 50, 100, 1, 0, 10000}, {"mutation_fixture", mutation_fixture, 1, 10, 30, 1, 1, 200}}) {
        if (! shipped && horizon_of(e.inst) > 1000)
            continue;
        auto off = root_state(e.inst, e.task, without, cumulative_proof_mutation::None{}, nullopt);
        auto unproved = root_state(e.inst, e.task, with, cumulative_proof_mutation::None{}, nullopt);
        auto proof_name = "cumulative_run_" + e.name;
        auto on = root_state(e.inst, e.task, with, cumulative_proof_mutation::None{}, proofs ? make_optional(proof_name) : nullopt);
        if (! off || ! on || ! unproved)
            fail(e.name + ": nothing was reached at the root");
        if (off->start_lb == e.start_lb && off->start_ub == e.start_ub && off->presence_ub == e.presence_ub)
            fail(e.name + ": something other than time-tabling already makes the push, so this fixture measures nothing");
        for (const auto & [what, got] : {pair{"with a proof", *on}, pair{"without one", *unproved}})
            if (got.start_lb != e.start_lb || got.start_ub != e.start_ub || got.presence_ub != e.presence_ub)
                fail(e.name + " " + what + ": expected start [" + std::to_string(e.start_lb) + ", " + std::to_string(e.start_ub) +
                    "] presence <= " + std::to_string(e.presence_ub) + ", got [" + std::to_string(got.start_lb) + ", " +
                    std::to_string(got.start_ub) + "] presence <= " + std::to_string(got.presence_ub));
        if (proofs) {
            auto runs = count_in_proof(proof_name, run_marker);
            auto lines = count_lines(proof_name);
            println(cerr, "cumulative run {}: start [{}, {}], {} run steps, {} proof lines", e.name, on->start_lb, on->start_ub, runs, lines);
            if (shipped && runs != e.runs)
                fail(e.name + ": expected " + std::to_string(e.runs) + " run steps, the proof takes " + std::to_string(runs));
            if (shipped && lines > e.max_lines)
                fail(e.name + ": " + std::to_string(lines) + " proof lines, against at most " + std::to_string(e.max_lines));
            verify_proof_and_clean_up(proof_name);
        }
    }

    // A task too tall for the resource on its own has nowhere to start, and a
    // run citing nobody says so in one step however wide its domain is.
    if (shipped) {
        auto too_tall = plain({{0, 10000}}, {{1, 1}}, {{3, 3}}, {2, 2});
        auto proof_name = string{"cumulative_run_too_tall"};
        if (root_state(too_tall, 0, with, cumulative_proof_mutation::None{}, proofs ? make_optional(proof_name) : nullopt))
            fail("too_tall: the root did not fail");
        if (proofs) {
            auto lines = count_lines(proof_name);
            println(cerr, "cumulative run too_tall: {} proof lines", lines);
            if (shipped && lines > 200)
                fail("too_tall: " + std::to_string(lines) + " proof lines");
            verify_proof_and_clean_up(proof_name);
        }
    }

    // Two tasks on one start variable, fixed at 3: the present one holds the
    // resource over [3, 5), so the optional one has nowhere to go. The run that
    // falsifies it cites the other task's pair flags, whose rows name the same
    // variable twice, once on each side.
    {
        Problem p;
        auto x = p.create_integer_variable(3_i, 3_i, "x");
        auto present = p.create_integer_variable(1_i, 1_i, "present");
        auto optional_presence = p.create_integer_variable(0_i, 1_i, "optional");
        auto two = [](IntegerVariableID a, IntegerVariableID b) { return vector<IntegerVariableID>{a, b}; };
        p.post(Cumulative{two(x, x), two(constant_variable(2_i), constant_variable(2_i)), two(constant_variable(1_i), constant_variable(1_i)),
            two(present, optional_presence), constant_variable(1_i)});
        auto proof_name = string{"cumulative_run_aliased"};
        optional<Integer> presence_ub;
        auto record = [&](const CurrentState & s) {
            if (! presence_ub)
                presence_ub = s.upper_bound(optional_presence);
            return false;
        };
        solve_with(
            p, SolveCallbacks{.solution = record, .trace = record}, proofs ? make_optional<ProofOptions>(ProofFileNames{proof_name}) : nullopt);
        if (presence_ub != 0_i)
            fail("aliased: the optional task was not falsified");
        if (proofs) {
            auto runs = count_in_proof(proof_name, run_marker);
            println(cerr, "cumulative run aliased: {} run steps", runs);
            if (shipped && runs != 1)
                fail("aliased: expected 1 run step, the proof takes " + std::to_string(runs));
            verify_proof_and_clean_up(proof_name);
        }
    }

    // Soundness and completeness, over the fixtures small enough to enumerate
    // and then over a random family: no solution may be lost, with or without
    // a proof being written. The family has to take run steps, or this says
    // nothing about them, so they are counted.
    vector<pair<string, Instance>> corpus{{"stairs", stairs({1, 1})}, {"falsify", falsify},
        {"small_long_push", plain({{0, 0}, {0, 40}}, {{20, 20}, {1, 1}}, {{1, 1}, {1, 1}}, {1, 1})},
        {"small_views", Instance{{{0, 0}, {0, 30}}, {{10, 10}, {1, 1}}, {{1, 1}, {1, 1}}, {{1, 1}, {1, 1}}, {1, 1}, true}}};

    mt19937 rand(*get_seed());
    for (int k = 0; k < 60;) {
        auto pick = [&](int lo, int hi) { return uniform_int_distribution<>(lo, hi)(rand); };
        auto n = pick(2, 4);
        auto capacity_lo = pick(1, 3);
        Instance inst;
        inst.capacity = pick(0, 4) == 0 ? pair{capacity_lo, capacity_lo + 1} : pair{capacity_lo, capacity_lo};
        inst.views = pick(0, 9) == 0;
        for (int i = 0; i < n; ++i) {
            // Mostly tasks fixed or nearly fixed, which make the plateaus, and
            // some with a wide start, which get pushed across them.
            auto s = pick(0, 6);
            inst.starts.emplace_back(s, s + (pick(0, 2) == 0 ? pick(4, 12) : pick(0, 1)));
            auto l = pick(1, 4);
            inst.lengths.emplace_back(l, pick(0, 5) == 0 ? l + 1 : l);
            auto h = pick(1, 2);
            inst.heights.emplace_back(h, pick(0, 7) == 0 ? h + 1 : h);
            inst.presences.push_back(pick(0, 4) == 0 ? pair{0, 1} : pair{1, 1});
        }
        if (size_of(inst) > 20'000)
            continue;
        corpus.emplace_back("random" + std::to_string(k++), inst);
    }

    int runs = 0;
    for (const auto & [name, inst] : corpus) {
        check_enumeration(name, inst, nullopt);
        if (proofs)
            runs += check_enumeration(name, inst, make_optional("cumulative_run_enum_" + name));
    }
    if (proofs && shipped && runs == 0)
        fail("no run step was taken over the enumeration corpus, so it checked nothing about them");
    println(cerr, "cumulative run: {} run steps over the enumeration corpus", runs);

    return EXIT_SUCCESS;
}
