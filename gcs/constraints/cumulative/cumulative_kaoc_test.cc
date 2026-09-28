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
    // Lengths and the capacity are constants. A height is a constant too
    // unless `height_ranges` gives it a range of more than one value, in which
    // case it is posted as a variable and enumerated alongside the starts. A
    // task flagged in `optional` gets a {0, 1} presence variable, enumerated
    // after the heights.
    struct Instance
    {
        vector<pair<int, int>> start_ranges;
        vector<int> lengths;
        vector<int> heights;
        int capacity;
        vector<pair<int, int>> height_ranges = {};
        vector<int> optional = {};
    };

    auto is_optional(const Instance & inst, size_t i) -> bool
    {
        return ! inst.optional.empty() && inst.optional[i];
    }

    auto has_optional_tasks(const Instance & inst) -> bool
    {
        for (size_t i = 0; i < inst.optional.size(); ++i)
            if (inst.optional[i])
                return true;
        return false;
    }

    auto height_range(const Instance & inst, size_t i) -> pair<int, int>
    {
        return inst.height_ranges.empty() ? pair{inst.heights[i], inst.heights[i]} : inst.height_ranges[i];
    }

    auto has_variable_heights(const Instance & inst) -> bool
    {
        for (size_t i = 0; i < inst.height_ranges.size(); ++i)
            if (inst.height_ranges[i].first != inst.height_ranges[i].second)
                return true;
        return false;
    }

    // What gets enumerated: the starts, then each variable height, then each
    // presence.
    auto all_ranges(const Instance & inst) -> vector<pair<int, int>>
    {
        auto ranges = inst.start_ranges;
        for (size_t i = 0; i < inst.start_ranges.size(); ++i)
            if (auto [lo, hi] = height_range(inst, i); lo != hi)
                ranges.emplace_back(lo, hi);
        for (size_t i = 0; i < inst.start_ranges.size(); ++i)
            if (is_optional(inst, i))
                ranges.emplace_back(0, 1);
        return ranges;
    }

    auto is_satisfying(const Instance & inst, const vector<int> & values) -> bool
    {
        auto n = inst.start_ranges.size();
        vector<int> heights, present;
        size_t next = n;
        for (size_t i = 0; i < n; ++i) {
            auto [lo, hi] = height_range(inst, i);
            heights.push_back(lo == hi ? lo : values[next++]);
        }
        for (size_t i = 0; i < n; ++i)
            present.push_back(is_optional(inst, i) ? values[next++] : 1);
        int t_lo = INT_MAX, t_hi = INT_MIN;
        for (size_t i = 0; i < n; ++i) {
            if (inst.lengths[i] == 0 || heights[i] == 0 || ! present[i])
                continue;
            t_lo = min(t_lo, values[i]);
            t_hi = max(t_hi, values[i] + inst.lengths[i] - 1);
        }
        for (int t = t_lo; t <= t_hi; ++t) {
            int load = 0;
            for (size_t i = 0; i < n; ++i)
                if (present[i] && values[i] <= t && t < values[i] + inst.lengths[i])
                    load += heights[i];
            if (load > inst.capacity)
                return false;
        }
        return true;
    }

    // Set from argv, so that a mutation lane runs the same fixtures the honest
    // lane does and differs only in what the certificate says. Global because
    // every fixture in the file has to carry it.
    CumulativeProofMutation the_mutation = cumulative_proof_mutation::None{};

    // Returns the variables in the order all_ranges() lists their ranges.
    auto post(Problem & p, const Instance & inst, CumulativeRules rules) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts;
        for (auto & [lo, hi] : inst.start_ranges)
            starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));

        if (! has_variable_heights(inst) && ! has_optional_tasks(inst)) {
            vector<Integer> lengths, heights;
            for (auto l : inst.lengths)
                lengths.push_back(Integer{l});
            for (auto h : inst.heights)
                heights.push_back(Integer{h});
            p.post(Cumulative{starts, lengths, heights, Integer{inst.capacity}}.with_rules(rules).with_proof_mutation(the_mutation));
            return starts;
        }

        vector<IntegerVariableID> lengths, heights, all = starts;
        for (auto l : inst.lengths)
            lengths.push_back(constant_variable(Integer{l}));
        for (size_t i = 0; i < inst.start_ranges.size(); ++i) {
            auto [lo, hi] = height_range(inst, i);
            if (lo == hi)
                heights.push_back(constant_variable(Integer{lo}));
            else {
                heights.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
                all.push_back(heights.back());
            }
        }
        if (! has_optional_tasks(inst)) {
            p.post(
                Cumulative{starts, lengths, heights, constant_variable(Integer{inst.capacity})}.with_rules(rules).with_proof_mutation(the_mutation));
            return all;
        }
        vector<IntegerVariableID> presences;
        for (size_t i = 0; i < inst.start_ranges.size(); ++i)
            if (is_optional(inst, i)) {
                presences.push_back(p.create_integer_variable(0_i, 1_i));
                all.push_back(presences.back());
            }
            else
                presences.push_back(constant_variable(1_i));
        p.post(Cumulative{starts, lengths, heights, presences, constant_variable(Integer{inst.capacity})}.with_rules(rules).with_proof_mutation(
            the_mutation));
        return all;
    }

    // Which rung of the overload ladder justified each conflict. The rules
    // share one certificate shape, so the marker is how a test tells them
    // apart: `ttheoc` is the shape with no time point strengthened, `kaoc` the
    // same shape with the knapsack cap on at least one of them.
    struct MarkerCounts
    {
        size_t oc = 0, ttoc = 0, ttheoc = 0, kaoc = 0;
        // Presence falsifications by energy (#550), by the rung that made them.
        size_t presence_oc = 0, presence_ttoc = 0, presence_ttheoc = 0, presence_kaoc = 0;

        [[nodiscard]] auto presence_total() const -> size_t
        {
            return presence_oc + presence_ttoc + presence_ttheoc + presence_kaoc;
        }

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
            if (line.find("cumulative overload presence") != string::npos) {
                if (line.find("rule=ttheoc") != string::npos)
                    ++counts.presence_ttheoc;
                else if (line.find("rule=kaoc") != string::npos)
                    ++counts.presence_kaoc;
                else if (line.find("rule=ttoc") != string::npos)
                    ++counts.presence_ttoc;
                else if (line.find("rule=oc") != string::npos)
                    ++counts.presence_oc;
                continue;
            }
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

    // Returns the overload markers the proof carried, counted before
    // check_results verifies the proof and deletes it.
    auto check_enumeration(const string & what, const Instance & inst, CumulativeRules rules, const optional<string> & proof_name) -> MarkerCounts
    {
        print(cerr, "cumulative kaoc {} starts={} lens={} hts={} c={}{}", what, inst.start_ranges, inst.lengths, inst.heights, inst.capacity,
            proof_name ? " with proofs:" : ":");
        cerr << flush;

        set<vector<int>> expected, actual;
        build_expected(expected, [&](const vector<int> & values) { return is_satisfying(inst, values); }, all_ranges(inst));
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto vars = post(p, inst, rules);
        solve_for_tests(p, proof_name, actual, tuple{vars});
        auto markers = proof_name ? count_markers(*proof_name) : MarkerCounts{};
        check_results(proof_name, expected, actual);
        return markers;
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
        build_expected(solutions, [&](const vector<int> & values) { return is_satisfying(inst, values); }, all_ranges(inst));
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

    // The same one rung down: a fixture the horizontally elastic cap refutes
    // at the root with no time point strengthened, which (TTOC) misses.
    auto check_elastic_only(const string & what, const Instance & inst) -> void
    {
        println(cerr, "cumulative kaoc {}: elastic-only differential", what);

        if (has_a_solution(inst))
            fail(what + ": the fixture is satisfiable, so refuting it would be a soundness bug");
        if (probe_root(inst, plain, nullopt).refuted)
            fail(what + ": (TTOC) already refutes it, so it is not a differential");

        auto probe = probe_root(inst, elastic, make_optional("cumulative_kaoc_" + what));
        if (! probe.refuted)
            fail(what + ": (TTHE-OC) did not refute it");
        if (probe.markers.ttheoc == 0)
            fail(what + ": refuted, but no conflict carried the ttheoc marker");
    }

    // What root propagation did to each optional task's presence, in the order
    // the instance lists the tasks. An upper bound of zero is a falsification.
    struct PresenceProbe
    {
        bool refuted = false;
        vector<Integer> presence_ub;
        MarkerCounts markers;

        [[nodiscard]] auto falsified(size_t k = 0) const -> bool
        {
            return k < presence_ub.size() && presence_ub[k] == 0_i;
        }
    };

    // `keep_proof` leaves the proof for a mutation lane's wrapper to check,
    // rather than verifying it here.
    auto probe_presence(const Instance & inst, CumulativeRules rules, const optional<string> & proof_name, bool keep_proof = false) -> PresenceProbe
    {
        Problem p;
        auto vars = post(p, inst, rules);
        size_t optional_count = 0;
        for (size_t i = 0; i < inst.start_ranges.size(); ++i)
            if (is_optional(inst, i))
                ++optional_count;
        vector<IntegerVariableID> presences(vars.end() - static_cast<long>(optional_count), vars.end());

        PresenceProbe probe;
        bool reached_a_node = false, found_a_solution = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                               found_a_solution = true;
                               return false;
                           },
                .trace = [&](const CurrentState & state) -> bool {
                    for (const auto & v : presences)
                        probe.presence_ub.push_back(state.upper_bound(v));
                    reached_a_node = true;
                    return false;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        probe.refuted = ! reached_a_node && ! found_a_solution;

        if (proof_name) {
            probe.markers = count_markers(*proof_name);
            if (! keep_proof)
                verify_proof_and_clean_up(*proof_name);
        }
        return probe;
    }

    // A fixture with one optional task, on which `rules` falsifies its presence
    // at the root by energy, and neither time-tabling alone nor `below` does.
    // The optional task is absent from every solution, so the falsification is
    // sound; the instance has solutions, so it is not a conflict fixture.
    auto check_presence_rung(const string & what, const Instance & inst, CumulativeRules rules, CumulativeRules below, size_t MarkerCounts::* rung)
        -> void
    {
        println(cerr, "cumulative kaoc {}: presence falsification by energy", what);

        set<vector<int>> solutions;
        build_expected(solutions, [&](const vector<int> & values) { return is_satisfying(inst, values); }, all_ranges(inst));
        if (solutions.empty())
            fail(what + ": the fixture has no solutions, so it tests a conflict rather than a falsification");
        for (const auto & solution : solutions)
            if (solution.back() != 0)
                fail(what + ": a solution has the optional task present, so falsifying it would be a soundness bug");

        if (probe_presence(inst, CumulativeRules{.overload = false}, nullopt).falsified())
            fail(what + ": time-tabling alone falsifies it, so the energy argument is not needed");
        if (probe_presence(inst, below, nullopt).falsified())
            fail(what + ": the rung below already falsifies it, so it is not a differential");

        auto probe = probe_presence(inst, rules, make_optional("cumulative_kaoc_" + what));
        if (probe.refuted)
            fail(what + ": refuted at the root, where it has solutions");
        if (! probe.falsified())
            fail(what + ": the optional task's presence was not falsified at the root");
        if (probe.markers.*rung == 0)
            fail(what + ": falsified, but not by the rung the fixture is for");

        check_enumeration(what + " enumeration", inst, rules, make_optional("cumulative_kaoc_" + what + "_enumeration"));
    }

    // Presence falsification by energy (#550): one fixture per rung, each with
    // one optional task, found by a random search for root differentials where
    // time-tabling's own falsification does not reach. Each is exactly one
    // unit over; its twin, one unit of capacity better off, must not fire.
    //
    // (OC'): the optional task would fill [0, 3) at height 4, and the height-4
    // unit task must run somewhere in [0, 3) too: 16 units in a window of 15.
    // It has no compulsory part, so time-tabling sees nothing.
    const Instance presence_oc{{{0, 0}, {0, 2}, {1, 3}}, {3, 1, 1}, {4, 4, 2}, 5, {}, {1, 0, 0}};
    // (TTOC): over [3, 8) the optional task and the height-5 one carry 34
    // units against 35, and the fixed task's compulsory part at 3 and 4, which
    // the window does not contain, adds the other two.
    const Instance presence_ttoc{{{3, 4}, {3, 5}, {1, 1}}, {4, 2, 4}, {6, 5, 1}, 7, {}, {1, 0, 0}};
    const Instance presence_ttheoc{{{1, 1}, {2, 3}, {0, 1}}, {3, 1, 3}, {4, 4, 1}, 6, {}, {1, 0, 0}};
    const Instance presence_kaoc{{{3, 3}, {0, 1}, {1, 4}}, {4, 2, 3}, {2, 1, 2}, 3, {}, {1, 0, 0}};
    // The optional task's height is a variable here, so its items are
    // converted as well as its energy.
    const Instance presence_kaoc_varh{{{1, 3}, {1, 1}, {2, 5}}, {2, 4, 3}, {2, 2, 1}, 3, {{2, 3}, {2, 3}, {1, 1}}, {0, 1, 0}};

    auto with_capacity(Instance inst, int capacity) -> Instance
    {
        inst.capacity = capacity;
        return inst;
    }

    // The mutation lanes' fixtures. The ones above do not serve: each of their
    // optional tasks has a fixed start, so once it is assumed present unit
    // propagation over the model fixes every one of its activity flags, and
    // neither the certificate nor its presence literal is ever needed. So these
    // were found by surveying 447 random falsifications, each with an optional
    // task whose start has room to move. Leaving the certificate out was
    // rejected on about two thirds of them; pointing the falsified task's
    // energy line at another task's presence on only three, which is the same
    // finding that retired the time-table falsification's WrongTask lane. The
    // last task of each is a far-off optional bystander, which is what
    // PresenceByEnergyWrongTask points at.
    struct PresenceMutationFixture
    {
        string name;
        Instance inst;
        CumulativeRules rules;
    };

    const vector<PresenceMutationFixture> presence_mutation_fixtures{
        {"mutation_oc", Instance{{{3, 4}, {1, 4}, {3, 3}, {30, 30}}, {3, 1, 4, 1}, {2, 1, 2, 1}, 3, {}, {1, 0, 0, 1}}, plain},
        {"mutation_kaoc", Instance{{{0, 0}, {3, 4}, {2, 3}, {30, 30}}, {3, 3, 3, 1}, {1, 2, 2, 1}, 3, {}, {0, 1, 0, 1}}, knapsack},
        {"mutation_ttheoc", Instance{{{1, 4}, {0, 3}, {1, 3}, {30, 30}}, {2, 3, 2, 1}, {6, 6, 6, 1}, 7, {}, {1, 0, 0, 1}}, knapsack},
        {"mutation_ttoc",
            Instance{{{1, 4}, {3, 6}, {1, 5}, {0, 1}, {2, 5}, {3, 4}, {30, 30}}, {4, 2, 4, 4, 3, 1, 1}, {1, 1, 1, 1, 1, 1, 1}, 2, {},
                {0, 0, 0, 0, 1, 0, 1}},
            plain}};

    // Two tasks of height two filling a capacity-two window of four exactly:
    // the optional one fits beside the other, so nothing may falsify it. The
    // PresenceByEnergyOneTooFar lane fires here anyway.
    const Instance exact_fit{{{0, 2}, {0, 2}}, {2, 2}, {2, 2}, 2, {}, {1, 0}};
}

auto main(int argc, char * argv[]) -> int
{
    // Before anything solves. Nothing in this file draws random *data* --- every
    // fixture is written out --- but the enumeration below branches with
    // random_branch_with_optional_seed, and without this its order comes from a
    // random_device: `--seed=N` was silently ignored, no seed was announced, and
    // cumulative_kaoc_enumeration.pbp differed between two runs of the same
    // binary. A failing lane could not be re-run, and the proof was useless as
    // a byte-diff reference.
    establish_and_announce_seed(argc, argv);

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
        else if (arg == "--mutate=presence_emit_nothing")
            the_mutation = cumulative_proof_mutation::PresenceByEnergyEmitNothing{}, mutating = true;
        else if (arg == "--mutate=presence_wrong_task")
            the_mutation = cumulative_proof_mutation::PresenceByEnergyWrongTask{}, mutating = true;
        else if (arg == "--mutate=presence_one_too_far")
            the_mutation = cumulative_proof_mutation::PresenceByEnergyOneTooFar{}, mutating = true;
        else if (arg.starts_with("--fixture="))
            mutated_fixture = arg.substr(arg.find('=') + 1);
        else if (arg == "--proof-files-basename" && a + 1 < argc)
            proof_basename = argv[++a];
    }

    // A presence mutation's fixture has solutions, so the proof has no conflict
    // in it: what it must have is the falsification being corrupted.
    if (mutating && (mutated_fixture.starts_with("mutation_") || mutated_fixture == "exact_fit")) {
        optional<PresenceMutationFixture> chosen;
        if (mutated_fixture == "exact_fit")
            chosen = PresenceMutationFixture{"exact_fit", exact_fit, plain};
        for (const auto & fixture : presence_mutation_fixtures)
            if (fixture.name == mutated_fixture)
                chosen = fixture;
        if (! chosen)
            fail("mutation mode: no fixture called " + mutated_fixture);
        if (probe_presence(chosen->inst, chosen->rules, make_optional(proof_basename), true).markers.presence_total() == 0)
            fail("mutation mode: nothing was falsified, so the proof has nothing corrupted in it");
        println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
        return EXIT_SUCCESS;
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

    // (TTHE-OC) on its own, which no lane used to fire: every fixture above
    // goes on to strengthen some time point, so it carries the kaoc marker.
    // Capacity two, and the window [1, 8) holds all five tasks, 13 units of
    // work against the 14 (TTOC) allows. But t = 1 is reachable only by the
    // length-four task and t = 7 only by the length-three one, both of height
    // one, so each of those points supplies one unit rather than two, and
    // that is one unit more than the window can spare.
    const Instance elastic_edges{{{2, 5}, {2, 5}, {1, 2}, {2, 5}, {3, 5}}, {2, 2, 4, 2, 3}, {1, 1, 1, 1, 1}, 2};
    check_elastic_only("elastic_edges", elastic_edges);

    // ... and its negative twin, with a third unit of capacity.
    {
        auto probe = probe_root(Instance{{{2, 5}, {2, 5}, {1, 2}, {2, 5}, {3, 5}}, {2, 2, 4, 2, 3}, {1, 1, 1, 1, 1}, 3}, knapsack, nullopt);
        if (probe.refuted)
            fail("elastic_edges negative twin: refuted an instance with room to spare");
    }

    // Variable heights (#550). A variable height is in the capacity row as the
    // bits of its contribution rather than as `h·active`, so the certificate
    // converts an item's bits back to `lb(h)·active` and weakens away the bits
    // of a task that is neither an item nor pinned.
    //
    // First, Cloutier & Quimper's Example 2 again, with every height a
    // variable over [2, 3]: counted at their lower bounds they are the
    // original fixture, and every item needs converting.
    check_knapsack_only("varh_cloutier_ex2",
        Instance{cloutier_ex2.start_ranges, cloutier_ex2.lengths, cloutier_ex2.heights, cloutier_ex2.capacity, {{2, 3}, {2, 3}, {2, 3}, {2, 3}}});

    // Instances a random sweep found, on which a step of the variable-height
    // certificate is load-bearing. Neither step is caught by the arithmetic
    // cross-check in the certificate, which counts what the rule charges
    // rather than what the lines say.
    //
    // With a non-item's bits left in the line, VeriPB rejects this one at the
    // root, on every seed: the only one of 12,000 random instances with
    // variable heights to show it there. The enumeration further down catches the same corruption
    // only on some seeds, since which of its conflicts meets it depends on the
    // branching.
    {
        const Instance varh_weaken_root{{{1, 3}, {0, 4}, {0, 3}, {3, 4}, {1, 3}, {0, 2}, {1, 5}}, {1, 3, 1, 2, 2, 2, 1}, {3, 1, 2, 3, 2, 1, 3}, 4,
            {{3, 3}, {1, 3}, {2, 3}, {3, 4}, {2, 2}, {1, 3}, {3, 3}}};
        if (has_a_solution(varh_weaken_root))
            fail("varh_weaken_root: the fixture is satisfiable, so refuting it would be a soundness bug");
        auto probe = probe_root(varh_weaken_root, knapsack, make_optional("cumulative_kaoc_varh_weaken_root"));
        if (! probe.refuted)
            fail("varh_weaken_root: (KAOC) did not refute it");
        if (probe.markers.kaoc == 0)
            fail("varh_weaken_root: refuted, but no conflict carried the kaoc marker");
    }

    // With the conversion left out, VeriPB rejects this one (and
    // varh_cloutier_ex2 above).
    {
        const Instance varh_convert{{{1, 1}, {1, 2}, {1, 2}}, {1, 4, 1}, {4, 4, 2}, 5, {{4, 4}, {4, 4}, {2, 4}}};
        auto markers = check_enumeration("varh_convert", varh_convert, knapsack, make_optional("cumulative_kaoc_varh_convert"));
        if (markers.ttheoc + markers.kaoc == 0)
            fail("varh_convert: no elastic conflict, so the conversion was not exercised");
    }
    {
        const Instance varh_weaken{
            {{0, 1}, {2, 5}, {3, 6}, {1, 4}, {0, 3}}, {2, 3, 2, 1, 3}, {1, 6, 3, 4, 6}, 7, {{1, 3}, {6, 7}, {3, 5}, {4, 6}, {6, 7}}};
        auto markers = check_enumeration("varh_weaken", varh_weaken, knapsack, make_optional("cumulative_kaoc_varh_weaken"));
        if (markers.ttheoc + markers.kaoc == 0)
            fail("varh_weaken: no elastic conflict, so the weakening was not exercised");
    }

    // Presence falsification by energy, a rung at a time.
    check_presence_rung("presence_oc", presence_oc, plain, CumulativeRules{.overload = false}, &MarkerCounts::presence_oc);
    check_presence_rung("presence_ttoc", presence_ttoc, plain, CumulativeRules{.profile_overload = false}, &MarkerCounts::presence_ttoc);
    check_presence_rung("presence_ttheoc", presence_ttheoc, elastic, plain, &MarkerCounts::presence_ttheoc);
    check_presence_rung("presence_kaoc", presence_kaoc, knapsack, elastic, &MarkerCounts::presence_kaoc);
    check_presence_rung("presence_kaoc_varh", presence_kaoc_varh, knapsack, elastic, &MarkerCounts::presence_kaoc);

    // ... their twins, one unit of capacity better off ...
    for (const auto & [what, inst, rules] :
        {tuple{"presence_oc", presence_oc, plain}, tuple{"presence_ttoc", presence_ttoc, plain}, tuple{"presence_ttheoc", presence_ttheoc, elastic},
            tuple{"presence_kaoc", presence_kaoc, knapsack}, tuple{"presence_kaoc_varh", presence_kaoc_varh, knapsack}})
        if (probe_presence(with_capacity(inst, inst.capacity + 1), rules, nullopt).falsified())
            fail(string{what} + " negative twin: falsified with a unit of capacity to spare");

    // ... the mutation lanes' fixtures, honestly: the task is falsified, the
    // bystander is not, and the proof verifies; and on exact_fit nothing is
    // falsified at all ...
    for (const auto & fixture : presence_mutation_fixtures) {
        auto probe = probe_presence(fixture.inst, fixture.rules, make_optional("cumulative_kaoc_" + fixture.name));
        if (! probe.falsified(0) || probe.falsified(1))
            fail(fixture.name + ": falsified the wrong tasks, so the mutation lanes would be testing something else");
    }
    {
        auto probe = probe_presence(exact_fit, knapsack, make_optional(string{"cumulative_kaoc_exact_fit"}));
        if (probe.falsified() || probe.markers.presence_total() != 0)
            fail("exact_fit: falsified a task with exactly enough room");
        if (! has_a_solution(exact_fit))
            fail("exact_fit: the fixture has no solution");
    }

    // The soundness net. A conflict-only rule can only ever lose solutions, so
    // a full enumeration against brute force with the proof verified is what
    // says the rule is not inventing conflicts.
    check_enumeration(
        "small enumeration", Instance{{{0, 4}, {0, 4}, {0, 4}}, {2, 2, 2}, {2, 2, 2}, 3}, knapsack, make_optional("cumulative_kaoc_enumeration"));

    return EXIT_SUCCESS;
}
