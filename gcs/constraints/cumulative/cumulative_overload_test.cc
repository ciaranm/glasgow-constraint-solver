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
using namespace gcs::innards;
using namespace gcs::test_innards;

namespace
{
    // A length and a height are each a range: `{v, v}` is the constant most
    // fixtures use, and `{v, w}` with v < w a decision variable, which the
    // check counts at `v` --- what the task is guaranteed to want, whatever the
    // search does with the rest of it (#689).
    struct Instance
    {
        vector<pair<int, int>> start_ranges;
        vector<pair<int, int>> lengths;
        vector<pair<int, int>> heights;
        int capacity;
    };

    auto length_is_var(const Instance & inst, size_t i) -> bool
    {
        return inst.lengths[i].first != inst.lengths[i].second;
    }

    auto height_is_var(const Instance & inst, size_t i) -> bool
    {
        return inst.heights[i].first != inst.heights[i].second;
    }

    // Every variable an assignment has to fix, in the order the solutions carry
    // them: the starts, then the variable lengths and then the variable heights,
    // each in task order.
    auto all_ranges(const Instance & inst) -> vector<pair<int, int>>
    {
        auto ranges = inst.start_ranges;
        for (size_t i = 0; i < inst.lengths.size(); ++i)
            if (length_is_var(inst, i))
                ranges.push_back(inst.lengths[i]);
        for (size_t i = 0; i < inst.heights.size(); ++i)
            if (height_is_var(inst, i))
                ranges.push_back(inst.heights[i]);
        return ranges;
    }

    auto is_satisfying(const Instance & inst, const vector<int> & vals) -> bool
    {
        auto n = inst.start_ranges.size();
        vector<int> l(n), h(n);
        size_t k = n;
        for (size_t i = 0; i < n; ++i)
            l[i] = length_is_var(inst, i) ? vals.at(k++) : inst.lengths[i].first;
        for (size_t i = 0; i < n; ++i)
            h[i] = height_is_var(inst, i) ? vals.at(k++) : inst.heights[i].first;

        int t_lo = INT_MAX, t_hi = INT_MIN;
        for (size_t i = 0; i < n; ++i) {
            if (l[i] == 0 || h[i] == 0)
                continue;
            t_lo = min(t_lo, vals[i]);
            t_hi = max(t_hi, vals[i] + l[i] - 1);
        }
        for (int t = t_lo; t <= t_hi; ++t) {
            int load = 0;
            for (size_t i = 0; i < n; ++i)
                if (vals[i] <= t && t < vals[i] + l[i])
                    load += h[i];
            if (load > inst.capacity)
                return false;
        }
        return true;
    }

    auto post(Problem & p, const Instance & inst, CumulativeRules rules, CumulativeProofMutation mutation = cumulative_proof_mutation::None{})
        -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts, all_vars;
        for (auto & [lo, hi] : inst.start_ranges) {
            starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
            all_vars.push_back(starts.back());
        }

        vector<IntegerVariableID> lengths, heights;
        for (size_t i = 0; i < inst.lengths.size(); ++i) {
            auto [lo, hi] = inst.lengths[i];
            if (! length_is_var(inst, i))
                lengths.push_back(constant_variable(Integer{lo}));
            else {
                lengths.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
                all_vars.push_back(lengths.back());
            }
        }
        for (size_t i = 0; i < inst.heights.size(); ++i) {
            auto [lo, hi] = inst.heights[i];
            if (! height_is_var(inst, i))
                heights.push_back(constant_variable(Integer{lo}));
            else {
                heights.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
                all_vars.push_back(heights.back());
            }
        }

        p.post(Cumulative{starts, lengths, heights, constant_variable(Integer{inst.capacity})}.with_rules(rules).with_proof_mutation(mutation));
        return all_vars;
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
        build_expected(expected, [&](const vector<int> & vals) { return is_satisfying(inst, vals); }, all_ranges(inst));
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto all_vars = post(p, inst, rules);
        solve_for_tests(p, proof_name, actual, tuple{all_vars});
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
    // task. Its length and height only have to be able to be positive.
    auto is_active(const Instance & inst, size_t i) -> bool
    {
        return inst.lengths[i].second > 0 && inst.heights[i].second > 0;
    }

    // A task the window-energy lemma can speak about, so a task the energy set
    // may contain. Mirrors prepare_overload_check: the encodings of the start
    // and of a variable length, a domain of exactly {0, 1} being direct-only
    // encoded and so having no order literals for the lemma's bridges to cancel
    // against. A {0, 1} *height* is not excluded, its conversion resolving to a
    // bare literal rather than to a defining line.
    auto is_eligible(const Instance & inst, size_t i) -> bool
    {
        if (! is_active(inst, i) || (inst.start_ranges[i].first == 0 && inst.start_ranges[i].second == 1))
            return false;
        return ! (length_is_var(inst, i) && inst.lengths[i].first == 0 && inst.lengths[i].second == 1);
    }

    // A task the energy set actually counts: one whose guaranteed duration and
    // guaranteed demand are both positive, so that there is energy to count. A
    // constant this small was turned away at prepare time; a variable one is
    // skipped by the candidate sweep instead, and both are then nothing but
    // profile.
    auto counts_energy(const Instance & inst, size_t i) -> bool
    {
        return is_eligible(inst, i) && inst.lengths[i].first > 0 && inst.heights[i].first > 0;
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
        // A task's guaranteed duration, which is what both its energy and its
        // mandatory part are measured in. Its *possible* duration is the
        // range's other end, and only the possibly-active range below uses it.
        auto p_of = [&](size_t i) { return inst.lengths[i].first; };
        auto h_of = [&](size_t i) { return inst.heights[i].first; };

        for (size_t wa = 0; wa < n; ++wa) {
            if (! counts_energy(inst, wa))
                continue;
            auto a = inst.start_ranges[wa].first;

            for (size_t wb = 0; wb < n; ++wb) {
                if (! counts_energy(inst, wb) || inst.start_ranges[wb].first < a)
                    continue;
                auto b = inst.start_ranges[wb].second + p_of(wb);
                if (b <= a)
                    continue;

                long long energy = 0, profile = 0;
                for (size_t i = 0; i < n; ++i) {
                    if (! is_active(inst, i))
                        continue;
                    auto est = inst.start_ranges[i].first, lct = inst.start_ranges[i].second + p_of(i);
                    if (counts_energy(inst, i) && est >= a && lct <= b) {
                        energy += static_cast<long long>(p_of(i)) * h_of(i);
                        continue;
                    }
                    if (! with_profile)
                        continue;
                    // the part of task i's mandatory part [lst, eet) =
                    // [ub(s), lb(s) + p) that lies inside the window
                    auto lst = inst.start_ranges[i].second, eet = inst.start_ranges[i].first + p_of(i);
                    for (auto t = max(lst, a); t < min(eet, b); ++t)
                        profile += h_of(i);
                }

                // Time points no task can occupy supply nothing to the window,
                // and the propagator does not count them either. What a task
                // could occupy runs to its *longest* duration, which is where
                // the flags it would be pinned through were laid down.
                long long slots = 0;
                for (auto t = a; t < b; ++t)
                    for (size_t i = 0; i < n; ++i)
                        if (is_active(inst, i) && t >= inst.start_ranges[i].first && t <= inst.start_ranges[i].second + inst.lengths[i].second - 1) {
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
    // Degenerate data is tested separately from the coprime kind, not mixed in
    // with it: equal heights, or heights and durations sharing a factor, make
    // arithmetic that is only right modulo that factor look right, so a suite
    // that mixed them could pass on the easy instances and say nothing about
    // the hard ones.
    enum class Data
    {
        Coprime,   ///< durations and heights all distinct primes
        Equal,     ///< one height for every task
        GcdHeavy,  ///< durations and heights all multiples of six
        UnitHeight ///< every height one, which is where the capacity is small
    };

    auto sharp_margin_instance(std::mt19937 & rand, int n, int horizon, Data data) -> optional<Instance>
    {
        static const vector<int> primes{29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113};
        static const vector<int> sixes{6, 12, 18, 24, 30, 36, 42, 48, 54, 60};

        auto pool = (data == Data::GcdHeavy) ? sixes : primes;
        std::shuffle(pool.begin(), pool.end(), rand);
        if (static_cast<size_t>(2 * n) > pool.size())
            return nullopt;

        Instance inst;
        long long energy = 0;
        for (int i = 0; i < n; ++i) {
            auto length = pool.at(static_cast<size_t>(i));
            auto height = [&]() {
                switch (data) {
                case Data::Coprime:
                case Data::GcdHeavy: return pool.at(static_cast<size_t>(n + i));
                case Data::Equal: return pool.at(static_cast<size_t>(n));
                case Data::UnitHeight: return 1;
                }
                return 1;
            }();
            if (length > horizon)
                return nullopt;
            inst.lengths.emplace_back(length, length);
            inst.heights.emplace_back(height, height);
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
    const Instance sharp{{{0, 7}, {0, 6}, {0, 7}, {0, 11}}, {{5, 5}, {6, 6}, {5, 5}, {1, 1}}, {{4, 4}, {3, 3}, {2, 2}, {1, 1}}, 4};

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
            // Only does anything under GCS_CUMULATIVE_ENCODING=both-recovering,
            // which the ctest entry for it sets; under any other encoding the
            // recovery does not run and the proof comes out honest.
            else if (arg == "--mutate=recover_wrong_checkpoint")
                mutation = cumulative_proof_mutation::RecoverFromWrongCheckpoint{};
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
    const Instance f1{{{0, 2}, {0, 2}, {0, 2}}, {{2, 2}, {2, 2}, {2, 2}}, {{1, 1}, {1, 1}, {1, 1}}, 1};

    // F1's negative twin: the same tasks with room to spread out. The widest
    // window [0, 8) now supplies exactly the 6 units the tasks need, so
    // nothing is overloaded and the rule must stay silent at the root.
    const Instance f1_twin{{{0, 6}, {0, 6}, {0, 6}}, {{2, 2}, {2, 2}, {2, 2}}, {{1, 1}, {1, 1}, {1, 1}}, 1};

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
    const Instance f2{
        {{0, 2}, {0, 2}, {0, 2}, {0, 2}, {1, 2}}, {{2, 2}, {2, 2}, {2, 2}, {2, 2}, {4, 4}}, {{1, 1}, {1, 1}, {1, 1}, {1, 1}, {1, 1}}, 2};

    // F2's negative twin: the same, with the straddling task moved past the
    // window, so its mandatory part [5, 8) contributes nothing to [0, 4) and
    // the window's demand is back to exactly its supply.
    const Instance f2_twin{
        {{0, 2}, {0, 2}, {0, 2}, {0, 2}, {4, 5}}, {{2, 2}, {2, 2}, {2, 2}, {2, 2}, {4, 4}}, {{1, 1}, {1, 1}, {1, 1}, {1, 1}, {1, 1}}, 2};

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

    // F3: a variable duration, which is what #689 is about. Two unit-height
    // tasks of length two and one whose length is a decision variable in
    // [1, 3], all free in [0, 2] against a capacity of one. The window [0, 4)
    // supplies four units and the two constant tasks want four of them, so the
    // conflict is exactly the one unit the variable-duration task is guaranteed
    // to occupy somewhere inside it.
    //
    // Nothing else in the propagator can find that unit. The task's mandatory
    // part is [lst, eet) = [2, 1), which is empty --- so the (TTOC) profile
    // term, which is where a variable duration used to end up in full, has
    // nothing to contribute, and neither has time-tabling. The energy set
    // counting the task at lb(l) is the whole of the difference.
    const Instance f3{{{0, 2}, {0, 2}, {0, 2}}, {{2, 2}, {2, 2}, {1, 3}}, {{1, 1}, {1, 1}, {1, 1}}, 1};

    // F3's negative twin: the same instance with the variable duration allowed
    // to be zero, so the task guarantees nothing and the window is back to
    // wanting exactly what it supplies. It is satisfiable --- the two constant
    // tasks tile [0, 4) and the third takes no time at all --- so this also
    // says that counting a task at anything above lb(l) would lose solutions.
    const Instance f3_twin{{{0, 2}, {0, 2}, {0, 2}}, {{2, 2}, {2, 2}, {0, 3}}, {{1, 1}, {1, 1}, {1, 1}}, 1};

    {
        auto with_rule = probe_root(f3, all_rules, proofs ? make_optional("cumulative_overload_f3") : nullopt);
        if (! with_rule.refuted)
            fail("F3: the overload check did not count the variable-duration task's guaranteed energy");
        if (proofs && with_rule.markers.oc != 1)
            fail("F3: expected exactly one (OC') marker, got " + std::to_string(with_rule.markers.oc));

        auto without_rule = probe_root(f3, no_overload, nullopt);
        if (without_rule.refuted)
            fail("F3: time-tabling alone refuted at the root, so the fixture proves nothing");
    }

    {
        auto with_rule = probe_root(f3_twin, all_rules, proofs ? make_optional("cumulative_overload_f3_twin") : nullopt);
        if (with_rule.refuted)
            fail("F3 twin: refuted at the root, but it is satisfiable");
        if (proofs && with_rule.markers.total() != 0)
            fail("F3 twin: the overload check claimed a conflict at the root");
    }

    // F4: F3's other half, on the demand rather than on the duration. Two unit
    // tasks of length two free in [0, 2] against a capacity of one, and a third
    // of length one whose *height* is a decision variable in [1, 3], free in
    // [0, 3]. The window [0, 4) supplies four units and the two constant tasks
    // want four, so the conflict is again exactly the one unit the third task
    // guarantees --- this time one unit of demand for one unit of time.
    //
    // What it exercises is the conversion rather than the lemma. A variable
    // height is not in a capacity row at all: what is there is the
    // bit-linearised contribution, so the task's activity has to be turned into
    // contribution terms before anything can cancel. Its mandatory part is
    // [3, 1), empty, so nothing else in the propagator can find that unit
    // either.
    const Instance f4{{{0, 2}, {0, 2}, {0, 3}}, {{2, 2}, {2, 2}, {1, 1}}, {{1, 1}, {1, 1}, {1, 3}}, 1};

    // F4's negative twin: the same instance with the variable demand allowed to
    // be zero, so the task guarantees nothing. Satisfiable --- the two constant
    // tasks tile [0, 4) and the third takes nothing --- so this is also what
    // says that counting a task at anything above lb(h) would lose solutions.
    const Instance f4_twin{{{0, 2}, {0, 2}, {0, 3}}, {{2, 2}, {2, 2}, {1, 1}}, {{1, 1}, {1, 1}, {0, 3}}, 1};

    {
        auto with_rule = probe_root(f4, all_rules, proofs ? make_optional("cumulative_overload_f4") : nullopt);
        if (! with_rule.refuted)
            fail("F4: the overload check did not count the variable-height task's guaranteed energy");
        if (proofs && with_rule.markers.oc != 1)
            fail("F4: expected exactly one (OC') marker, got " + std::to_string(with_rule.markers.oc));

        auto without_rule = probe_root(f4, no_overload, nullopt);
        if (without_rule.refuted)
            fail("F4: time-tabling alone refuted at the root, so the fixture proves nothing");
    }

    {
        auto with_rule = probe_root(f4_twin, all_rules, proofs ? make_optional("cumulative_overload_f4_twin") : nullopt);
        if (with_rule.refuted)
            fail("F4 twin: refuted at the root, but it is satisfiable");
        if (proofs && with_rule.markers.total() != 0)
            fail("F4 twin: the overload check claimed a conflict at the root");
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
        for (auto [data, label] : {pair{Data::Coprime, "coprime"}, pair{Data::Equal, "equal_heights"}, pair{Data::GcdHeavy, "gcd_heavy"},
                 pair{Data::UnitHeight, "unit_heights"}}) {
            int found = 0;
            for (int attempt = 0; attempt < 4000 && found < 3; ++attempt) {
                std::uniform_int_distribution<> horizon_dist(120, 240);
                auto inst = sharp_margin_instance(rand, 3, horizon_dist(rand), data);
                if (! inst)
                    continue;
                ++found;

                auto name = "cumulative_overload_sharp_" + string{label} + "_" + std::to_string(found);
                println(cerr, "cumulative overload sharp margin {} lens={} hts={} c={} horizon={}", label, inst->lengths, inst->heights,
                    inst->capacity, inst->start_ranges[0].second + inst->lengths[0].first);
                auto probe = probe_root(*inst, only_overload, proofs ? make_optional(name) : nullopt);
                if (! probe.refuted)
                    fail("sharp margin: the overload check did not refute at the root");
                if (proofs && probe.markers.oc != 1)
                    fail("sharp margin: expected exactly one (OC') marker");
            }
            if (found == 0)
                fail("sharp margin: the " + string{label} + " generator produced nothing to test");
        }
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
        // At most one task per instance gets a variable duration, and by a
        // narrow spread: every extra value multiplies the brute-force
        // enumeration each of these instances is also checked against, and what
        // is wanted here is 300 instances rather than one wide one.
        std::uniform_int_distribution<> n_dist(2, 4), lo_dist(-3, 4), span_dist(0, 4), len_dist(0, 3), ht_dist(0, 3), cap_dist(0, 4),
            spread_dist(0, 2);

        size_t fired = 0, verified = 0, with_var_length = 0, with_var_height = 0;
        for (int k = 0; k < 300; ++k) {
            Instance inst;
            auto n = n_dist(rand);
            auto var_length_task = std::uniform_int_distribution<>(0, n - 1)(rand);
            auto var_height_task = std::uniform_int_distribution<>(0, n - 1)(rand);
            auto length_spread = spread_dist(rand), height_spread = spread_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand), span = span_dist(rand);
                inst.start_ranges.emplace_back(lo, lo + span);
                auto len = len_dist(rand);
                inst.lengths.emplace_back(len, len + (i == var_length_task ? length_spread : 0));
                auto ht = ht_dist(rand);
                inst.heights.emplace_back(ht, ht + (i == var_height_task ? height_spread : 0));
            }
            inst.capacity = cap_dist(rand);
            if (length_spread > 0)
                ++with_var_length;
            if (height_spread > 0)
                ++with_var_height;

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
        if (with_var_length == 0 || with_var_height == 0)
            fail("oracle cross-check: no instance in the corpus had a variable duration or no instance had a variable demand");
        println(cerr, "oracle cross-check: {} of 300 instances overloaded at the root, {} with a variable duration and {} with a variable demand",
            fired, with_var_length, with_var_height);
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
        check_opb_unaffected("f3", f3);
        check_opb_unaffected("f4", f4);

        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(2, 4), lo_dist(-2, 4), span_dist(0, 4), len_dist(0, 3), ht_dist(0, 3), cap_dist(0, 4),
            spread_dist(0, 3);
        for (int k = 0; k < 20; ++k) {
            Instance inst;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand), span = span_dist(rand);
                inst.start_ranges.emplace_back(lo, lo + span);
                auto len = len_dist(rand);
                inst.lengths.emplace_back(len, len + spread_dist(rand));
                auto ht = ht_dist(rand);
                inst.heights.emplace_back(ht, ht + spread_dist(rand));
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
    // F3's pair, where the search is what makes them worth running: branching
    // on the length variable raises lb(l) below the root, so the energy rows
    // here are ones whose length bound is not the declared one --- the case the
    // boundary pin cannot pay for and a unit RUP has to.
    check_enumeration("f3", f3, all_rules, proofs ? make_optional("cumulative_overload_enum_f3") : nullopt);
    check_enumeration("f3_twin", f3_twin, all_rules, proofs ? make_optional("cumulative_overload_enum_f3_twin") : nullopt);
    // And F4's, where the search branches on the height variable instead, so
    // the conversion runs at bounds the boundary pin cannot pay for.
    check_enumeration("f4", f4, all_rules, proofs ? make_optional("cumulative_overload_enum_f4") : nullopt);
    check_enumeration("f4_twin", f4_twin, all_rules, proofs ? make_optional("cumulative_overload_enum_f4_twin") : nullopt);

    return EXIT_SUCCESS;
}
