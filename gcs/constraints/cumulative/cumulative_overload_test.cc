#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <climits>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <optional>
#include <set>
#include <sstream>
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
using std::ifstream;
using std::make_optional;
using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

namespace
{
    // Every fixture in this file is an all-constant instance: the overload
    // check only speaks about tasks whose length and height are constants.
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

    auto post(Problem & p, const Instance & inst, CumulativeRules rules) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts;
        for (auto & [lo, hi] : inst.start_ranges)
            starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));

        vector<Integer> lengths, heights;
        for (auto l : inst.lengths)
            lengths.push_back(Integer{l});
        for (auto h : inst.heights)
            heights.push_back(Integer{h});

        p.post(Cumulative{starts, lengths, heights, Integer{inst.capacity}}.with_rules(rules));
        return starts;
    }

    // How many times each overload rule left its marker in a proof file. The
    // propagator writes one comment per conflict it justifies, tagged with the
    // rule that made it, so a test can tell "the rule fired" from "the rule
    // was compiled in and never triggered" --- and, on a negative twin, insist
    // that it did not fire at all.
    struct MarkerCounts
    {
        size_t oc = 0, ttoc = 0;

        [[nodiscard]] auto total() const -> size_t
        {
            return oc + ttoc;
        }
    };

    auto count_markers(const string & proof_name) -> MarkerCounts
    {
        MarkerCounts counts;
        ifstream proof{proof_name + ".pbp"};
        if (! proof) {
            println(cerr, "could not read {}.pbp to count overload markers", proof_name);
            std::exit(EXIT_FAILURE);
        }
        string line;
        while (getline(proof, line)) {
            if (line.find("cumulative overload conflict") == string::npos)
                continue;
            if (line.find("rule=ttoc") != string::npos)
                ++counts.ttoc;
            else if (line.find("rule=oc") != string::npos)
                ++counts.oc;
        }
        return counts;
    }

    // What one propagation at the root did: whether it refuted the instance
    // outright, and which overload rules fired doing so. Stopping at the first
    // search node keeps the marker counts attributable to root reasoning --- a
    // satisfiable instance would otherwise accumulate markers from conflicts
    // deep in the search, which says nothing about the fixture.
    struct RootProbe
    {
        bool refuted = false;
        MarkerCounts markers;
    };

    auto probe_root(const Instance & inst, CumulativeRules rules, const optional<string> & proof_name) -> RootProbe
    {
        Problem p;
        post(p, inst, rules);

        RootProbe probe;
        bool reached_a_node = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return false; },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    return false;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        probe.refuted = ! reached_a_node;

        if (proof_name) {
            probe.markers = count_markers(*proof_name);
            verify_proof_and_clean_up(*proof_name);
        }
        return probe;
    }

    // A full enumeration against brute force, with the proof verified. This is
    // the soundness net: the overload check only ever reports conflicts, so a
    // bug in it removes solutions.
    auto check_enumeration(const string & what, const Instance & inst, CumulativeRules rules, const optional<string> & proof_name) -> void
    {
        print(cerr, "cumulative overload {} starts={} lens={} hts={} c={}{}", what, inst.start_ranges, inst.lengths, inst.heights, inst.capacity,
            proof_name ? " with proofs:" : ":");
        cerr << flush;

        set<vector<int>> expected, actual;
        build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(inst, starts); }, inst.start_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto starts = post(p, inst, rules);
        solve_for_tests(p, proof_name, actual, tuple{starts});
        check_results(proof_name, expected, actual);
    }

    auto fail(const string & message) -> void
    {
        println(cerr, "cumulative overload test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    // The two rules, written out from their definitions, over a fully general
    // double loop and sharing no code with the propagator. Used to classify
    // random instances: the propagator must refute at the root exactly when
    // this says a window is overloaded.
    auto oracle_says_overloaded(const Instance & inst, bool with_profile) -> bool
    {
        auto n = inst.start_ranges.size();
        for (size_t wa = 0; wa < n; ++wa)
            for (size_t wb = 0; wb < n; ++wb) {
                auto a = inst.start_ranges[wa].first;
                auto b = inst.start_ranges[wb].second + inst.lengths[wb];
                if (b <= a)
                    continue;

                long long energy = 0, profile = 0;
                for (size_t i = 0; i < n; ++i) {
                    if (inst.lengths[i] <= 0 || inst.heights[i] <= 0)
                        continue;
                    auto est = inst.start_ranges[i].first, lct = inst.start_ranges[i].second + inst.lengths[i];
                    if (est >= a && lct <= b) {
                        energy += static_cast<long long>(inst.lengths[i]) * inst.heights[i];
                        continue;
                    }
                    if (! with_profile)
                        continue;
                    // the part of task i's mandatory part that lies inside the
                    // window: [lst, eet) = [ub(s), lb(s) + p)
                    auto lst = inst.start_ranges[i].second, eet = inst.start_ranges[i].first + inst.lengths[i];
                    for (auto t = max(lst, a); t < min(eet, b); ++t)
                        profile += inst.heights[i];
                }

                // Time points no task can occupy supply nothing to the window,
                // and the propagator does not count them either.
                long long slots = 0;
                for (auto t = a; t < b; ++t)
                    for (size_t i = 0; i < n; ++i)
                        if (inst.lengths[i] > 0 && inst.heights[i] > 0 && t >= inst.start_ranges[i].first &&
                            t <= inst.start_ranges[i].second + inst.lengths[i] - 1) {
                            ++slots;
                            break;
                        }

                if (energy + profile > static_cast<long long>(inst.capacity) * slots)
                    return true;
            }
        return false;
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    const CumulativeRules all_rules{};
    const CumulativeRules no_overload{.time_table = true, .overload = false, .profile_overload = false};
    const CumulativeRules no_profile{.time_table = true, .overload = true, .profile_overload = false};

    auto proofs = can_run_veripb();

    // F1: three unit-height tasks of length two, each free in [0, 2], sharing
    // a resource of capacity one. Every mandatory part is empty (lst = 2 is
    // not before eet = 2), so time-tabling sees nothing at all; but the window
    // [0, 4) must hold 3 x 2 = 6 units of energy and supplies 1 x 4 = 4.
    const Instance f1{{{0, 2}, {0, 2}, {0, 2}}, {2, 2, 2}, {1, 1, 1}, 1};

    // F1's negative twin: the same tasks with room to spread out. The widest
    // window [0, 8) now supplies exactly the 6 units the tasks need, so
    // nothing is overloaded and the rule must stay silent at the root.
    const Instance f1_twin{{{0, 6}, {0, 6}, {0, 6}}, {2, 2, 2}, {1, 1, 1}, 1};

    {
        auto with_rule = probe_root(f1, all_rules, proofs ? make_optional("cumulative_overload_f1") : nullopt);
        if (! with_rule.refuted)
            fail("F1: the overload check did not refute at the root");
        if (proofs && with_rule.markers.oc != 1)
            fail("F1: expected exactly one (OC') marker, got " + std::to_string(with_rule.markers.oc));
        if (proofs && with_rule.markers.ttoc != 0)
            fail("F1: (TTOC) fired where (OC') alone was enough");

        auto without_rule = probe_root(f1, no_overload, nullopt);
        if (without_rule.refuted)
            fail("F1: time-tabling alone refuted at the root, so the fixture proves nothing");
    }

    {
        auto with_rule = probe_root(f1_twin, all_rules, proofs ? make_optional("cumulative_overload_f1_twin") : nullopt);
        if (with_rule.refuted)
            fail("F1 twin: refuted at the root, but it is satisfiable");
        if (proofs && with_rule.markers.total() != 0)
            fail("F1 twin: the overload check claimed a conflict at the root");
    }

    // F2: (TTOC), the profile strengthening. Four length-two, height-one tasks
    // free in [0, 2] fill the window [0, 4) exactly: energy 8 against a supply
    // of 2 x 4, so (OC') is silent. The fifth task runs past the end of the
    // window (est 1, lct 6), so it is not in the window's energy set at all,
    // but its mandatory part [2, 5) puts two units of load inside the window
    // regardless of where it starts --- and 8 + 2 > 8.
    //
    // Time-tabling can say nothing here: no task in the window has a mandatory
    // part, and the fifth task's one unit of load never blocks a height-one
    // task under a capacity of two, so no bound moves either.
    const Instance f2{{{0, 2}, {0, 2}, {0, 2}, {0, 2}, {1, 2}}, {2, 2, 2, 2, 4}, {1, 1, 1, 1, 1}, 2};

    // F2's negative twin: the same, with the straddling task moved past the
    // window, so its mandatory part [5, 8) contributes nothing to [0, 4) and
    // the window's demand is back to exactly its supply.
    const Instance f2_twin{{{0, 2}, {0, 2}, {0, 2}, {0, 2}, {4, 5}}, {2, 2, 2, 2, 4}, {1, 1, 1, 1, 1}, 2};

    {
        auto with_rule = probe_root(f2, all_rules, proofs ? make_optional("cumulative_overload_f2") : nullopt);
        if (! with_rule.refuted)
            fail("F2: the (TTOC) strengthening did not refute at the root");
        if (proofs && with_rule.markers.ttoc != 1)
            fail("F2: expected exactly one (TTOC) marker, got " + std::to_string(with_rule.markers.ttoc));

        auto without_profile = probe_root(f2, no_profile, nullopt);
        if (without_profile.refuted)
            fail("F2: (OC') alone refuted at the root, so the fixture does not test (TTOC)");

        auto without_rule = probe_root(f2, no_overload, nullopt);
        if (without_rule.refuted)
            fail("F2: time-tabling alone refuted at the root, so the fixture proves nothing");
    }

    {
        auto with_rule = probe_root(f2_twin, all_rules, proofs ? make_optional("cumulative_overload_f2_twin") : nullopt);
        if (with_rule.refuted)
            fail("F2 twin: refuted at the root, but it is satisfiable");
        if (proofs && with_rule.markers.total() != 0)
            fail("F2 twin: the overload check claimed a conflict at the root");
    }

    // The solutions must survive the new rule: it only ever reports conflicts,
    // so a bug in it shows up here as a missing solution.
    check_enumeration("f1", f1, all_rules, proofs ? make_optional("cumulative_overload_enum_f1") : nullopt);
    check_enumeration("f1_twin", f1_twin, all_rules, proofs ? make_optional("cumulative_overload_enum_f1_twin") : nullopt);
    check_enumeration("f2", f2, all_rules, proofs ? make_optional("cumulative_overload_enum_f2") : nullopt);
    check_enumeration("f2_twin", f2_twin, all_rules, proofs ? make_optional("cumulative_overload_enum_f2_twin") : nullopt);

    return EXIT_SUCCESS;
}
