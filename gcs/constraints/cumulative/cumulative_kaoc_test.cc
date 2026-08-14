#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <climits>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <optional>
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
using namespace gcs::innards;
using namespace gcs::test_innards;

namespace
{
    // Every fixture here is all-constant: the horizontally elastic rules
    // decline a variable height outright, and the window-energy lemma the
    // certificate cites wants a constant length.
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

    // Set from argv, so that a mutation lane runs the same fixtures the honest
    // lane does and differs only in what the certificate says. Global because
    // every fixture in the file has to carry it.
    CumulativeProofMutation the_mutation = cumulative_proof_mutation::None{};

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

        p.post(Cumulative{starts, lengths, heights, Integer{inst.capacity}}.with_rules(rules).with_proof_mutation(the_mutation));
        return starts;
    }

    // Which rung of the overload ladder justified each conflict. The rules
    // share one certificate shape, so the marker is how a test tells them
    // apart: `ttheoc` is the shape with no time point strengthened, `kaoc` the
    // same shape with the knapsack cap on at least one of them.
    struct MarkerCounts
    {
        size_t oc = 0, ttoc = 0, ttheoc = 0, kaoc = 0;

        [[nodiscard]] auto total() const -> size_t
        {
            return oc + ttoc + ttheoc + kaoc;
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
            if (line.find("rule=ttheoc") != string::npos)
                ++counts.ttheoc;
            else if (line.find("rule=kaoc") != string::npos)
                ++counts.kaoc;
            else if (line.find("rule=ttoc") != string::npos)
                ++counts.ttoc;
            else if (line.find("rule=oc") != string::npos)
                ++counts.oc;
        }
        return counts;
    }

    struct RootProbe
    {
        bool refuted = false;
        MarkerCounts markers;
    };

    auto solve_root_only(const Instance & inst, CumulativeRules rules, const optional<string> & proof_name) -> bool
    {
        Problem p;
        post(p, inst, rules);

        bool reached_a_node = false, found_a_solution = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                               found_a_solution = true;
                               return false;
                           },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    return false;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        return ! reached_a_node && ! found_a_solution;
    }

    auto probe_root(const Instance & inst, CumulativeRules rules, const optional<string> & proof_name) -> RootProbe
    {
        RootProbe probe;
        probe.refuted = solve_root_only(inst, rules, proof_name);

        if (proof_name) {
            probe.markers = count_markers(*proof_name);
            verify_proof_and_clean_up(*proof_name);
        }
        return probe;
    }

    auto check_enumeration(const string & what, const Instance & inst, CumulativeRules rules, const optional<string> & proof_name) -> void
    {
        print(cerr, "cumulative kaoc {} starts={} lens={} hts={} c={}{}", what, inst.start_ranges, inst.lengths, inst.heights, inst.capacity,
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
        println(cerr, "cumulative kaoc test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    const CumulativeRules plain{};
    const CumulativeRules elastic{.elastic_overload = true};
    const CumulativeRules knapsack{.elastic_overload = true, .knapsack_overload = true};

    // Cloutier & Quimper, CP 2026, Example 2. Four tasks of height 2 sharing a
    // resource of capacity 3, each two time units long, all inside [0, 7).
    // (OC') sees 3 x 7 = 21 units of energy available against the 16 required
    // and says nothing; so does the horizontally elastic cap, since all four
    // tasks could be at every time point. But no subset of the heights
    // {2, 2, 2, 2} sums to 3, so a time point supplies 2 rather than 3, the
    // window supplies 14, and 16 > 14 is a conflict. The paper calls this the
    // parity test; here it is the strengthening utility's divisibility fast
    // path, since every coefficient shares the factor 2.
    const Instance cloutier_ex2{{{0, 5}, {0, 5}, {0, 5}, {0, 5}}, {2, 2, 2, 2}, {2, 2, 2, 2}, 3};

    // Heights {3, 3, 5, 5} under a capacity of 7, in the window [0, 8). Their
    // gcd is 1, so the divisibility fast path does not apply and the
    // strengthening has to run its layered dynamic programme: the reachable
    // sums are 0, 3, 5, 6, 8, 10, 11, 13, 16, so 6 is the most a time point
    // can supply, not 7. Over eight time points that is 48 against the 53 the
    // tasks require --- where (OC') sees 56 available and declines, and so
    // does the horizontally elastic cap, since between them the four tasks
    // could take 16 at any time point. No task has a compulsory part, so the
    // profile says nothing either.
    const Instance dp_path{{{0, 5}, {0, 5}, {0, 4}, {0, 5}}, {3, 3, 4, 3}, {3, 3, 5, 5}, 7};

    // The same rule again, but on a window where one task has a compulsory
    // part: the length-four task in [0, 6) must be running throughout [2, 4).
    // Neither fixture above has one at all, which matters because the
    // certificate's one asymmetric step --- weakening a contained task's
    // compulsory times back out of its energy line, since the availability
    // side was charged for them --- is a no-op without one, and a mutation of
    // a no-op passes every check there is.
    //
    // Over [0, 6) at capacity 7: 33 units required once the compulsory part is
    // taken off, against 36 the elastic cap allows and 30 the knapsack does,
    // since {3, 3, 3, 3} reaches only 6 of the 7 free and {3, 3, 3} only 3 of
    // the 4 the profile leaves at the two compulsory time points.
    const Instance compulsory{{{0, 2}, {0, 3}, {0, 3}, {0, 3}}, {4, 3, 3, 3}, {3, 3, 3, 3}, 7};

    auto has_a_solution(const Instance & inst) -> bool
    {
        set<vector<int>> solutions;
        build_expected(solutions, [&](const vector<int> & starts) { return is_satisfying(inst, starts); }, inst.start_ranges);
        return ! solutions.empty();
    }

    // A fixture the knapsack cap is supposed to refute at the root, and the
    // rungs below it are supposed to miss. Both halves matter: a rule that
    // fires everywhere proves nothing, and one that never fires proves less.
    auto check_knapsack_only(const string & what, const Instance & inst) -> void
    {
        println(cerr, "cumulative kaoc {}: knapsack-only differential", what);

        // A conflict rule firing on a satisfiable instance is the failure this
        // whole file is here to catch, and the rungs below cannot catch it for
        // us: they decline on this fixture by construction.
        if (has_a_solution(inst))
            fail(what + ": the fixture is satisfiable, so refuting it would be a soundness bug");
        if (probe_root(inst, plain, nullopt).refuted)
            fail(what + ": (TTOC) already refutes it, so it is not a differential");
        if (probe_root(inst, elastic, nullopt).refuted)
            fail(what + ": (TTHE-OC) already refutes it, so it is not a knapsack differential");

        auto probe = probe_root(inst, knapsack, make_optional("cumulative_kaoc_" + what));
        if (! probe.refuted)
            fail(what + ": (KAOC) did not refute it");
        if (probe.markers.kaoc == 0)
            fail(what + ": refuted, but no conflict carried the kaoc marker");
    }
}

auto main(int argc, char * argv[]) -> int
{
    // A mutation lane runs one fixture and expects VeriPB to reject it. Which
    // fixture matters: `cloutier_ex2` takes the strengthening's divisibility
    // fast path and `dp_path` its layered dynamic programme, and a mutation
    // that bites on one need not bite on the other.
    string mutated_fixture, proof_basename = "cumulative_kaoc_mutation";
    bool mutating = false;
    for (int a = 1; a < argc; ++a) {
        string arg = argv[a];
        if (arg == "--mutate=claim_one_better")
            the_mutation = cumulative_proof_mutation::ClaimOneBetterAvailability{}, mutating = true;
        else if (arg == "--mutate=strengthen_one_fewer")
            the_mutation = cumulative_proof_mutation::StrengthenOneFewer{}, mutating = true;
        else if (arg == "--mutate=capacity")
            the_mutation = cumulative_proof_mutation::OmitCapacityLine{}, mutating = true;
        else if (arg.starts_with("--fixture="))
            mutated_fixture = arg.substr(arg.find('=') + 1);
        else if (arg == "--proof-files-basename" && a + 1 < argc)
            proof_basename = argv[++a];
    }

    if (mutating) {
        const auto & inst = mutated_fixture == "dp_path" ? dp_path : mutated_fixture == "compulsory" ? compulsory : cloutier_ex2;
        if (! solve_root_only(inst, knapsack, make_optional(proof_basename)))
            fail("mutation mode: the fixture was not refuted, so the proof has no conflict in it");
        println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
        return EXIT_SUCCESS;
    }

    check_knapsack_only("cloutier_ex2", cloutier_ex2);

    // The same shape with one more time point to play with, which is exactly
    // enough: 8 units of time for 8 units of work. Nothing may fire.
    {
        auto probe = probe_root(Instance{{{0, 6}, {0, 6}, {0, 6}, {0, 6}}, {2, 2, 2, 2}, {2, 2, 2, 2}, 3}, knapsack, nullopt);
        if (probe.refuted)
            fail("cloutier_ex2 negative twin: refuted a satisfiable instance");
    }

    check_knapsack_only("dp_path", dp_path);

    // ... and its negative twin, one unit of capacity better off. 8 is now a
    // reachable sum (3 + 5), so the knapsack cap buys nothing at all.
    {
        auto probe = probe_root(Instance{{{0, 5}, {0, 5}, {0, 4}, {0, 5}}, {3, 3, 4, 3}, {3, 3, 5, 5}, 8}, knapsack, nullopt);
        if (probe.refuted)
            fail("dp_path negative twin: refuted an instance the knapsack cap cannot reach");
    }

    check_knapsack_only("compulsory", compulsory);

    // ... and its negative twin: give the length-four task one more place to
    // go and its compulsory part vanishes, which frees the two time points the
    // conflict was leaning on.
    {
        auto probe = probe_root(Instance{{{0, 4}, {0, 3}, {0, 3}, {0, 3}}, {4, 3, 3, 3}, {3, 3, 3, 3}, 7}, knapsack, nullopt);
        if (probe.refuted)
            fail("compulsory negative twin: refuted an instance the rule should not reach");
    }

    // The soundness net. A conflict-only rule can only ever lose solutions, so
    // a full enumeration against brute force with the proof verified is what
    // says the rule is not inventing conflicts.
    check_enumeration(
        "small enumeration", Instance{{{0, 4}, {0, 4}, {0, 4}}, {2, 2, 2}, {2, 2, 2}, 3}, knapsack, make_optional("cumulative_kaoc_enumeration"));

    return EXIT_SUCCESS;
}
