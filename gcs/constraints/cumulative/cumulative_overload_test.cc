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
#include <random>
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

    auto post(Problem & p, const Instance & inst, CumulativeRules rules, CumulativeProofMutation mutation = cumulative_proof_mutation::None{})
        -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts;
        for (auto & [lo, hi] : inst.start_ranges)
            starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));

        vector<Integer> lengths, heights;
        for (auto l : inst.lengths)
            lengths.push_back(Integer{l});
        for (auto h : inst.heights)
            heights.push_back(Integer{h});

        p.post(Cumulative{starts, lengths, heights, Integer{inst.capacity}}.with_rules(rules).with_proof_mutation(mutation));
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

    auto solve_root_only(const Instance & inst, CumulativeRules rules, CumulativeProofMutation mutation, const optional<string> & proof_name) -> bool
    {
        Problem p;
        post(p, inst, rules, mutation);

        // Refuted means the root propagation reached a contradiction: neither
        // a search node nor a solution. The solution check is not redundant --- an
        // instance whose variables are all fixed by propagation is answered
        // without ever branching, so no node is ever traced.
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
        probe.refuted = solve_root_only(inst, rules, cumulative_proof_mutation::None{}, proof_name);

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

    auto read_file(const string & name) -> string
    {
        ifstream in{name, std::ios::binary};
        if (! in)
            fail("could not read " + name);
        return string{std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
    }

    // The OPB is the statement being verified, and nothing in the overload
    // check may reach it: every fact it establishes is a derivation inside the
    // proof. So the model must come out byte-identical however the rule is
    // configured --- including under the mutations, which are proof-only too.
    //
    // VeriPB will happily verify a correct proof of the wrong model, so this
    // is not a tidiness check: an inference that quietly became a model axiom
    // would leave every proof in this file verifying and prove nothing about
    // the solver.
    auto check_opb_unaffected(const string & what, const Instance & inst) -> void
    {
        const string on = "cumulative_overload_opb_on", off = "cumulative_overload_opb_off", mutated = "cumulative_overload_opb_mutated";

        solve_root_only(inst, CumulativeRules{}, cumulative_proof_mutation::None{}, on);
        solve_root_only(
            inst, CumulativeRules{.time_table = true, .overload = false, .profile_overload = false}, cumulative_proof_mutation::None{}, off);
        solve_root_only(inst, CumulativeRules{}, cumulative_proof_mutation::OverstateWindowEnergy{}, mutated);

        auto with_rule = read_file(on + ".opb");
        if (with_rule != read_file(off + ".opb"))
            fail("OPB differs with and without the overload check, on " + what);
        if (with_rule != read_file(mutated + ".opb"))
            fail("OPB differs under a proof mutation, on " + what);

        for (const auto & name : {on, off, mutated})
            dispose_of_proof_files(name);
    }

    // A task raises the load profile at all --- what prepare() calls an active
    // task.
    auto is_active(const Instance & inst, size_t i) -> bool
    {
        return inst.lengths[i] > 0 && inst.heights[i] > 0;
    }

    // A task the window-energy lemma can speak about, so a task the energy set
    // may contain. Mirrors prepare_overload_check: everything here is a
    // constant already, so all that is left is the start's encoding.
    auto is_eligible(const Instance & inst, size_t i) -> bool
    {
        return is_active(inst, i) && ! (inst.start_ranges[i].first == 0 && inst.start_ranges[i].second == 1);
    }

    // The two rules, written out from their definitions over a plain double
    // loop, sharing no code with the propagator. Used to classify random
    // instances: with time-tabling turned off, the propagator must refute at
    // the root exactly when this says some window is overloaded.
    //
    // The window candidates match the propagator's: a is an earliest start
    // time, and b a latest completion time *of a task with est >= a*. A window
    // whose b comes from a task starting before a has the same energy set as
    // the shorter window ending at that set's own largest lct, and (with
    // time-tabling on, so that no time point is loaded past the capacity)
    // shrinking to it cannot lose more profile than supply. An empty energy
    // set is the remaining case, and a window overloaded by profile alone is a
    // time-table overflow.
    auto oracle_says_overloaded(const Instance & inst, bool with_profile) -> bool
    {
        auto n = inst.start_ranges.size();
        for (size_t wa = 0; wa < n; ++wa) {
            if (! is_eligible(inst, wa))
                continue;
            auto a = inst.start_ranges[wa].first;

            for (size_t wb = 0; wb < n; ++wb) {
                if (! is_eligible(inst, wb) || inst.start_ranges[wb].first < a)
                    continue;
                auto b = inst.start_ranges[wb].second + inst.lengths[wb];
                if (b <= a)
                    continue;

                long long energy = 0, profile = 0;
                for (size_t i = 0; i < n; ++i) {
                    if (! is_active(inst, i))
                        continue;
                    auto est = inst.start_ranges[i].first, lct = inst.start_ranges[i].second + inst.lengths[i];
                    if (is_eligible(inst, i) && est >= a && lct <= b) {
                        energy += static_cast<long long>(inst.lengths[i]) * inst.heights[i];
                        continue;
                    }
                    if (! with_profile)
                        continue;
                    // the part of task i's mandatory part [lst, eet) =
                    // [ub(s), lb(s) + p) that lies inside the window
                    auto lst = inst.start_ranges[i].second, eet = inst.start_ranges[i].first + inst.lengths[i];
                    for (auto t = max(lst, a); t < min(eet, b); ++t)
                        profile += inst.heights[i];
                }

                // Time points no task can occupy supply nothing to the window,
                // and the propagator does not count them either.
                long long slots = 0;
                for (auto t = a; t < b; ++t)
                    for (size_t i = 0; i < n; ++i)
                        if (is_active(inst, i) && t >= inst.start_ranges[i].first && t <= inst.start_ranges[i].second + inst.lengths[i] - 1) {
                            ++slots;
                            break;
                        }

                if (energy + profile > static_cast<long long>(inst.capacity) * slots)
                    return true;
            }
        }
        return false;
    }

    // Sharp-margin instances: n tasks whose durations and heights are distinct
    // primes, all free to start anywhere inside one window [0, H), with the
    // capacity set so that the window's energy exceeds its supply by between
    // one and three units.
    //
    // At a margin that small every coefficient in the emitted derivation is
    // load-bearing: drop one capacity line, or lose one unit from one task's
    // window energy, and the contradiction is gone. Pairwise-coprime data
    // keeps any arithmetic that happens to be right modulo a common factor
    // from passing by luck.
    auto sharp_margin_instance(std::mt19937 & rand, int n, int horizon) -> optional<Instance>
    {
        static const vector<int> primes{29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113};

        vector<int> pool = primes;
        std::shuffle(pool.begin(), pool.end(), rand);
        if (static_cast<size_t>(2 * n) > pool.size())
            return nullopt;

        Instance inst;
        long long energy = 0;
        for (int i = 0; i < n; ++i) {
            auto length = pool.at(static_cast<size_t>(i));
            auto height = pool.at(static_cast<size_t>(n + i));
            if (length > horizon)
                return nullopt;
            inst.lengths.push_back(length);
            inst.heights.push_back(height);
            inst.start_ranges.emplace_back(0, horizon - length);
            energy += static_cast<long long>(length) * height;
        }

        auto capacity = (energy - 1) / horizon;
        if (capacity < 1)
            return nullopt;
        auto margin = energy - capacity * horizon;
        if (margin < 1 || margin > 3)
            return nullopt;

        inst.capacity = static_cast<int>(capacity);
        return inst;
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    const CumulativeRules all_rules{};
    const CumulativeRules no_overload{.time_table = true, .overload = false, .profile_overload = false};
    const CumulativeRules no_profile{.time_table = true, .overload = true, .profile_overload = false};
    // Isolate the energy reasoning: with time-tabling off, the only conflict
    // the propagator can report is an overload one.
    const CumulativeRules only_overload{.time_table = false, .overload = true, .profile_overload = true};

    auto proofs = can_run_veripb();

    // A sharp-margin instance: four tasks that must all run inside [0, 12),
    // needing 5x4 + 6x3 + 5x2 + 1x1 = 49 units of energy where a capacity of
    // four supplies 48. Every task can start early enough to have no mandatory
    // part at all and every height fits under the capacity, so time-tabling
    // has nothing to say --- neither a profile overflow nor a single blocked
    // time --- which leaves the energy argument as the only way to see the
    // conflict.
    //
    // The mutation runs below corrupt this instance's proof, because a margin
    // of exactly one is what makes every step of the derivation load-bearing:
    // one capacity line fewer, or one unit less energy from one task, and the
    // contradiction is gone.
    const Instance sharp{{{0, 7}, {0, 6}, {0, 7}, {0, 11}}, {5, 6, 5, 1}, {4, 3, 2, 1}, 4};

    // Mutation mode: emit one deliberately corrupted proof of `sharp` and
    // stop, for run_test_and_expect_verify_failure.bash to hand to veripb.
    // The corruption is in the proof only, so the solve still refutes; if it
    // ever stops doing so, the harness would be checking an empty proof.
    {
        optional<CumulativeProofMutation> mutation;
        string proof_basename = "cumulative_overload_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=energy")
                mutation = cumulative_proof_mutation::OverstateWindowEnergy{};
            else if (arg == "--mutate=capacity")
                mutation = cumulative_proof_mutation::OmitCapacityLine{};
            else if (arg == "--mutate=window")
                mutation = cumulative_proof_mutation::ShrinkLemmaWindow{};
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            if (! solve_root_only(sharp, all_rules, *mutation, make_optional(proof_basename)))
                fail("mutation mode: the sharp-margin instance was not refuted, so the proof is empty");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

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

    // The sharp-margin fixture itself, with time-tabling out of the way so
    // that only the energy argument can reach the conflict.
    {
        auto with_rule = probe_root(sharp, only_overload, proofs ? make_optional("cumulative_overload_sharp") : nullopt);
        if (! with_rule.refuted)
            fail("sharp: the overload check did not refute at the root");
        if (proofs && with_rule.markers.oc != 1)
            fail("sharp: expected exactly one (OC') marker, got " + std::to_string(with_rule.markers.oc));

        auto without_rule = probe_root(sharp, no_overload, nullopt);
        if (without_rule.refuted)
            fail("sharp: time-tabling alone refuted at the root, so the fixture proves nothing");
    }

    // Sharp margins at scale, over durations and heights drawn from distinct
    // primes: the arithmetic here has no small factors to hide behind, and
    // every window is wide enough that the derivation runs to hundreds of
    // steps.
    {
        std::mt19937 rand(*get_seed());
        int found = 0;
        for (int attempt = 0; attempt < 4000 && found < 4; ++attempt) {
            std::uniform_int_distribution<> horizon_dist(120, 240);
            auto inst = sharp_margin_instance(rand, 3, horizon_dist(rand));
            if (! inst)
                continue;
            ++found;

            auto name = "cumulative_overload_primes_" + std::to_string(found);
            println(cerr, "cumulative overload sharp margin lens={} hts={} c={} horizon={}", inst->lengths, inst->heights, inst->capacity,
                inst->start_ranges[0].second + inst->lengths[0]);
            auto probe = probe_root(*inst, only_overload, proofs ? make_optional(name) : nullopt);
            if (! probe.refuted)
                fail("sharp margin: the overload check did not refute at the root");
            if (proofs && probe.markers.oc != 1)
                fail("sharp margin: expected exactly one (OC') marker");
        }
        if (found == 0)
            fail("sharp margin: the generator produced nothing to test");
    }

    // Oracle cross-check. Over a random corpus, with time-tabling off so that
    // an overload conflict is the only conflict available, the propagator must
    // refute at the root exactly when the from-the-definition oracle says a
    // window is overloaded --- which catches both under- and over-firing.
    {
        std::mt19937 rand(*get_seed());
        // Start domains reach below zero: a window then runs over negative
        // time points, where the order literals the lemma bridges to are on a
        // signed bit encoding (issue #553's shape).
        std::uniform_int_distribution<> n_dist(2, 4), lo_dist(-3, 4), span_dist(0, 4), len_dist(0, 3), ht_dist(0, 3), cap_dist(0, 4);

        size_t fired = 0, verified = 0;
        for (int k = 0; k < 300; ++k) {
            Instance inst;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand), span = span_dist(rand);
                inst.start_ranges.emplace_back(lo, lo + span);
                inst.lengths.push_back(len_dist(rand));
                inst.heights.push_back(ht_dist(rand));
            }
            inst.capacity = cap_dist(rand);

            auto oracle = oracle_says_overloaded(inst, true);
            // Verify a proof for the first few conflicts, rather than all of
            // them: the cross-check is about which instances fire, and the
            // fixtures above are where the derivation itself is scrutinised.
            auto name = (oracle && verified < 10) ? make_optional("cumulative_overload_oracle_" + std::to_string(verified)) : nullopt;
            auto probe = probe_root(inst, only_overload, proofs ? name : nullopt);

            if (probe.refuted != oracle) {
                println(cerr, "oracle disagreement on starts={} lens={} hts={} c={}: oracle says {}, propagator says {}", inst.start_ranges,
                    inst.lengths, inst.heights, inst.capacity, oracle, probe.refuted);
                fail("oracle cross-check");
            }
            if (probe.refuted) {
                ++fired;
                if (name)
                    ++verified;
                if (proofs && name && probe.markers.total() != 1)
                    fail("oracle cross-check: a refutation left no overload marker");
            }

            // The rule must not cost solutions, whatever the oracle says.
            check_enumeration("random_" + std::to_string(k), inst, all_rules, nullopt);
        }

        if (fired == 0)
            fail("oracle cross-check: no instance in the corpus overloaded, so nothing was compared");
        println(cerr, "oracle cross-check: {} of 300 instances overloaded at the root", fired);
    }

    // Two tasks sharing one start variable. Each still has its own per-time
    // flags, so each gets its own window-energy line, and the two lines cancel
    // against their own terms in the capacity lines --- but they RUP the same
    // order literals of the same variable along the way. Three unit-height
    // tasks of length two in [0, 2] against a capacity of one, two of them
    // sharing a start.
    {
        Problem p;
        auto shared = p.create_integer_variable(0_i, 2_i);
        auto other = p.create_integer_variable(0_i, 2_i);
        vector<IntegerVariableID> starts{shared, shared, other};
        p.post(Cumulative{starts, vector<Integer>{2_i, 2_i, 2_i}, vector<Integer>{1_i, 1_i, 1_i}, 1_i}.with_rules(only_overload));

        bool reached_a_node = false, found_a_solution = false;
        auto name = "cumulative_overload_dup";
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                               found_a_solution = true;
                               return false;
                           },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    return false;
                }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{name}) : nullopt);

        if (reached_a_node || found_a_solution)
            fail("dup: the overload check did not refute at the root");
        if (proofs) {
            if (count_markers(name).total() != 1)
                fail("dup: expected exactly one overload marker");
            verify_proof_and_clean_up(name);
        }
    }

    // Nothing the overload check does may reach the model.
    {
        check_opb_unaffected("f1", f1);
        check_opb_unaffected("f2", f2);
        check_opb_unaffected("sharp", sharp);

        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(2, 4), lo_dist(-2, 4), span_dist(0, 4), len_dist(0, 3), ht_dist(0, 3), cap_dist(0, 4);
        for (int k = 0; k < 20; ++k) {
            Instance inst;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand), span = span_dist(rand);
                inst.start_ranges.emplace_back(lo, lo + span);
                inst.lengths.push_back(len_dist(rand));
                inst.heights.push_back(ht_dist(rand));
            }
            inst.capacity = cap_dist(rand);
            check_opb_unaffected("random_" + std::to_string(k), inst);
        }
    }

    // The solutions must survive the new rule: it only ever reports conflicts,
    // so a bug in it shows up here as a missing solution.
    check_enumeration("f1", f1, all_rules, proofs ? make_optional("cumulative_overload_enum_f1") : nullopt);
    check_enumeration("f1_twin", f1_twin, all_rules, proofs ? make_optional("cumulative_overload_enum_f1_twin") : nullopt);
    check_enumeration("f2", f2, all_rules, proofs ? make_optional("cumulative_overload_enum_f2") : nullopt);
    check_enumeration("f2_twin", f2_twin, all_rules, proofs ? make_optional("cumulative_overload_enum_f2_twin") : nullopt);

    return EXIT_SUCCESS;
}
