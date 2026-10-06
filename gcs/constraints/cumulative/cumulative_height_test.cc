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

// The height rule (#1239): a present task that runs for at least one time unit
// takes its height wherever it starts, so its height can be no more than the
// most room any of its placements leaves under the capacity.

namespace
{
    // The comment the rule's justification writes, which tests count: a rule
    // that never fires makes every other assertion about it vacuous.
    const string height_marker = "has room for a height of at most";

    // Every size is a range, `{v, v}` being a constant. A presence of `{1, 1}`
    // is a task with no presence variable at all; an instance where every task
    // has one is posted without presences.
    struct Instance
    {
        vector<pair<int, int>> starts, lengths, heights, presences;
        pair<int, int> capacity;
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
        vector<IntegerVariableID> heights, all_vars;
    };

    auto post(Problem & p, const Instance & inst, CumulativeRules rules, CumulativeProofMutation mutation = cumulative_proof_mutation::None{})
        -> Posted
    {
        Posted posted;
        auto make = [&](const pair<int, int> & r, const string & name) -> IntegerVariableID {
            if (! is_var(r))
                return constant_variable(Integer{r.first});
            auto v = p.create_integer_variable(Integer{r.first}, Integer{r.second}, name);
            return v;
        };
        vector<IntegerVariableID> starts, lengths, presences;
        for (size_t i = 0; i < inst.starts.size(); ++i)
            starts.push_back(p.create_integer_variable(Integer{inst.starts[i].first}, Integer{inst.starts[i].second}, "start" + std::to_string(i)));
        posted.all_vars = starts;
        for (size_t i = 0; i < inst.lengths.size(); ++i) {
            lengths.push_back(make(inst.lengths[i], "length" + std::to_string(i)));
            if (is_var(inst.lengths[i]))
                posted.all_vars.push_back(lengths.back());
        }
        for (size_t i = 0; i < inst.heights.size(); ++i) {
            posted.heights.push_back(make(inst.heights[i], "height" + std::to_string(i)));
            if (is_var(inst.heights[i]))
                posted.all_vars.push_back(posted.heights.back());
        }
        for (size_t i = 0; i < inst.presences.size(); ++i) {
            presences.push_back(make(inst.presences[i], "present" + std::to_string(i)));
            if (is_var(inst.presences[i]))
                posted.all_vars.push_back(presences.back());
        }
        auto capacity = make(inst.capacity, "capacity");
        if (is_var(inst.capacity))
            posted.all_vars.push_back(capacity);

        auto cumulative = has_presences(inst) ? Cumulative{starts, lengths, posted.heights, presences, capacity}
                                              : Cumulative{starts, lengths, posted.heights, capacity};
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

    auto fail(const string & message) -> void
    {
        println(cerr, "cumulative height: {}", message);
        exit(EXIT_FAILURE);
    }

    /// The upper bound each height is left with once root propagation has run.
    auto root_height_upper_bounds(const Instance & inst, CumulativeRules rules, CumulativeProofMutation mutation, const optional<string> & proof_name)
        -> optional<vector<int>>
    {
        Problem p;
        auto heights = post(p, inst, rules, mutation).heights;

        optional<vector<int>> bounds;
        auto record = [&](const CurrentState & s) {
            if (! bounds) {
                bounds.emplace();
                for (const auto & h : heights)
                    bounds->push_back(static_cast<int>(s.upper_bound(h).raw_value));
            }
            return false;
        };
        solve_with(
            p, SolveCallbacks{.solution = record, .trace = record}, proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        return bounds;
    }

    /// Exactly the brute-force solutions, with or without a proof, and the
    /// number of times the rule fired doing it (-1 without a proof).
    auto check_enumeration(const string & what, const Instance & inst, const optional<string> & proof_name) -> int
    {
        print(cerr, "cumulative height {} starts={} lens={} hts={} pres={} cap={}{}", what, inst.starts, inst.lengths, inst.heights, inst.presences,
            inst.capacity, proof_name ? " with proofs:" : ":");
        cerr << flush;

        set<vector<int>> expected, actual;
        build_expected(expected, [&](const vector<int> & vals) { return is_satisfying(inst, vals); }, all_ranges(inst));
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto all_vars = post(p, inst, CumulativeRules{}).all_vars;
        solve_for_tests(p, proof_name, actual, tuple{all_vars});
        auto fired = proof_name ? count_in_proof(*proof_name, height_marker) : -1;
        check_results(proof_name, expected, actual);
        return fired;
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
    const CumulativeRules without{.time_table = false};
    const CumulativeRules with{};

    auto plain = [](vector<pair<int, int>> starts, vector<pair<int, int>> lengths, vector<pair<int, int>> heights, pair<int, int> capacity) {
        return Instance{starts, lengths, heights, vector<pair<int, int>>(starts.size(), {1, 1}), capacity};
    };

    // The issue's instance: nothing is mandatory anywhere, so the capacity is
    // all the rule has to go on, and it is enough.
    const auto issue = plain({{0, 4}, {0, 4}, {0, 4}}, {{2, 2}, {2, 2}, {2, 2}}, {{2, 2}, {2, 2}, {2, 1000}}, {5, 5});

    // The task in the middle runs for three time units somewhere in [0, 6),
    // between one fixed task of height 4 over [0, 2) and another of height 2
    // over [4, 6). Starting at 0 or 1 leaves it room for 1; at 2 or 3, for 3.
    // Counted at 4 it is blocked at times 1 and 4, which is a two-step chain,
    // each step citing a different fixed task.
    const auto profile = plain({{0, 0}, {0, 3}, {4, 4}}, {{2, 2}, {3, 3}, {2, 2}}, {{4, 4}, {1, 10}, {2, 2}}, {5, 5});

    // The same with the middle task's start fixed at 0, where its whole
    // footprint is mandatory: one step.
    const auto fixed_start = plain({{0, 0}, {0, 0}, {4, 4}}, {{2, 2}, {3, 3}, {2, 2}}, {{4, 4}, {1, 10}, {2, 2}}, {5, 5});

    // A variable length is counted at the least it can be, and a variable
    // capacity at the most.
    const auto var_length_capacity = plain({{0, 0}, {0, 1}, {4, 4}}, {{2, 2}, {2, 4}, {2, 2}}, {{4, 4}, {1, 10}, {2, 2}}, {4, 5});

    // Two variable heights against each other. Both are mandatory at time 2,
    // where each guarantees the other's lower bound of 1, so neither has room
    // for more than 5 anywhere.
    const auto two_variable = plain({{0, 2}, {0, 2}}, {{3, 3}, {3, 3}}, {{1, 9}, {1, 9}}, {6, 6});

    // Not to fire: a length that may be zero takes nothing anywhere...
    const auto zero_length = plain({{0, 0}, {0, 3}, {4, 4}}, {{2, 2}, {0, 3}, {2, 2}}, {{4, 4}, {1, 10}, {2, 2}}, {5, 5});
    // ...and a task that may be absent may have any height at all.
    const auto optional_task =
        Instance{{{0, 0}, {0, 3}, {4, 4}}, {{2, 2}, {3, 3}, {2, 2}}, {{4, 4}, {1, 10}, {2, 2}}, {{1, 1}, {0, 1}, {1, 1}}, {5, 5}};
    // A present one is no different from a task with no presence at all. The
    // optional task out at time 6 is there only so that the constraint has
    // presences.
    const auto present_task = Instance{{{0, 0}, {0, 3}, {4, 4}, {6, 6}}, {{2, 2}, {3, 3}, {2, 2}, {1, 1}}, {{4, 4}, {1, 10}, {2, 2}, {1, 1}},
        {{1, 1}, {1, 1}, {1, 1}, {0, 1}}, {5, 5}};

    // Three tasks crowded around times 8 and 9, two of them variable in
    // height. The first one, mandatory nowhere, has room for 3 wherever it
    // starts, because the other two are mandatory over [8, 10). Found by a
    // random search for an instance whose chain is load-bearing: on the
    // fixtures above, unit propagation over the start-checkpoint rows closes
    // the conclusion with no chain at all, so a corruption of the chain there
    // verifies anyway, as it did for presence falsification. Here both the
    // chain and its contributing pins are needed.
    const auto crowded = plain({{7, 9}, {7, 8}, {7, 8}}, {{2, 2}, {3, 3}, {3, 3}}, {{3, 12}, {2, 11}, {2, 2}}, {7, 7});

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<CumulativeProofMutation> mutation;
        // Not `crowded` for the claim one too far: its height comes down to its
        // own lower bound, so one further empties the domain at the root and
        // there is nothing left to have reached.
        const Instance * fixture = &crowded;
        string proof_basename = "cumulative_height_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=toofar") {
                mutation = cumulative_proof_mutation::LowerHeightOneTooFar{};
                fixture = &profile;
            }
            else if (arg == "--mutate=emit_nothing")
                mutation = cumulative_proof_mutation::HeightEmitNothing{};
            else if (arg == "--mutate=drop")
                mutation = cumulative_proof_mutation::DropHeightContributor{};
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            if (! root_height_upper_bounds(*fixture, with, *mutation, make_optional(proof_basename)))
                fail("mutation mode: nothing was reached, so the proof is empty");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // The rule fires at the root, and lowers the height exactly as far as the
    // profile supports. `task` is the height being measured.
    for (const auto & [name, inst, task, expected] :
        vector<tuple<string, Instance, size_t, int>>{{"issue", issue, 2, 5}, {"profile", profile, 1, 3}, {"fixed_start", fixed_start, 1, 1},
            {"var_length_capacity", var_length_capacity, 1, 1}, {"two_variable", two_variable, 0, 5}, {"zero_length", zero_length, 1, 10},
            {"optional_task", optional_task, 1, 10}, {"present_task", present_task, 1, 3}, {"crowded", crowded, 0, 3}}) {
        auto off = root_height_upper_bounds(inst, without, cumulative_proof_mutation::None{}, nullopt);
        auto proof_name = "cumulative_height_" + name;
        auto on = root_height_upper_bounds(inst, with, cumulative_proof_mutation::None{}, proofs ? make_optional(proof_name) : nullopt);
        if (! off || ! on)
            fail(name + ": nothing was reached at the root");
        if (off->at(task) != inst.heights.at(task).second)
            fail(name + ": something other than the rule already lowers the height, so this fixture measures nothing");
        if (on->at(task) != expected)
            fail(name + ": expected the height to come down to " + std::to_string(expected) + ", got " + std::to_string(on->at(task)));
        println(cerr, "cumulative height {}: task {} height ub {} -> {}", name, task, off->at(task), on->at(task));
        if (proofs) {
            auto markers = count_in_proof(proof_name, height_marker);
            if ((expected < inst.heights.at(task).second) != (markers > 0))
                fail(name + ": the rule's marker appears " + std::to_string(markers) + " times");
            verify_proof_and_clean_up(proof_name);
        }
    }

    // Soundness and completeness, over the fixtures and then over a random
    // family whose heights reach past the capacity: the rule may not lose a
    // solution, with or without a proof being written. The family has to make
    // the rule fire, or this says nothing about it, so the firings are counted.
    vector<pair<string, Instance>> corpus{{"profile", profile}, {"fixed_start", fixed_start}, {"var_length_capacity", var_length_capacity},
        {"two_variable", two_variable}, {"zero_length", zero_length}, {"optional_task", optional_task}, {"present_task", present_task},
        {"crowded", crowded}, {"issue_small", plain({{0, 4}, {0, 4}, {0, 4}}, {{2, 2}, {2, 2}, {2, 2}}, {{2, 2}, {2, 2}, {2, 12}}, {5, 5})}};

    mt19937 rand(*get_seed());
    for (int k = 0; k < 40;) {
        auto pick = [&](int lo, int hi) { return uniform_int_distribution<>(lo, hi)(rand); };
        auto n = pick(2, 3);
        auto capacity_lo = pick(1, 4);
        Instance inst;
        inst.capacity = pick(0, 3) == 0 ? pair{capacity_lo, capacity_lo + 1} : pair{capacity_lo, capacity_lo};
        for (int i = 0; i < n; ++i) {
            auto s = pick(0, 3);
            inst.starts.emplace_back(s, s + pick(0, 3));
            auto l = pick(0, 3);
            inst.lengths.emplace_back(l, pick(0, 4) == 0 ? l + 1 : l);
            auto h = pick(0, 3);
            inst.heights.emplace_back(h, pick(0, 1) == 0 ? h + pick(1, 5) : h);
            inst.presences.push_back(pick(0, 4) == 0 ? pair{0, 1} : pair{1, 1});
        }
        if (size_of(inst) > 20'000)
            continue;
        corpus.emplace_back("random" + std::to_string(k++), inst);
    }

    int fired = 0;
    for (const auto & [name, inst] : corpus) {
        check_enumeration(name, inst, nullopt);
        if (proofs)
            fired += check_enumeration(name, inst, make_optional("cumulative_height_enum_" + name));
    }
    if (proofs && fired == 0)
        fail("the rule never fired over the enumeration corpus, so it checked nothing about it");
    println(cerr, "cumulative height: the rule fired {} times over the enumeration corpus", fired);

    return EXIT_SUCCESS;
}
