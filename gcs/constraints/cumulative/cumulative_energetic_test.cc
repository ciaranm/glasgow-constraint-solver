/* Energetic edge-finding for Cumulative, and its certificate (#755).
 *
 * `cumulative_ttef_test.cc` covers the time-table form, which charges a window
 * a contained task's whole energy plus a non-contained one's mandatory part in
 * it. This one covers the energetic form, which charges *every* task its
 * guaranteed energy --- the least overlap its execution interval can have with
 * the window over the starts its bounds still allow. That subsumes both: a
 * contained task's guaranteed energy is its whole energy, and a non-contained
 * one's is at least its mandatory part and usually more.
 *
 * The certificate is edge-finding's with a different set of rows cited, and
 * what makes it cheap is that the extra energy needs no pins: the guaranteed
 * figure is exactly what `derive_guarded_window_energy` establishes, guarded by
 * the task's own bounds, which the reason carries whether or not the window
 * contains the task. Where TTEF pays 2.93 reason-backed pin lines per firing
 * for its profile term, this pays none.
 *
 * So the mutation lane that matters is `drop_energetic`, which leaves out the
 * row of a task the window does *not* contain: `drop` removes a row plain
 * edge-finding would have cited anyway and says nothing about what is new here.
 */

#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <climits>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <variant>
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
using std::ranges::any_of;

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
        vector<Integer> lengths, heights;
        for (size_t i = 0; i < inst.start_ranges.size(); ++i) {
            starts.push_back(
                p.create_integer_variable(Integer{inst.start_ranges[i].first}, Integer{inst.start_ranges[i].second}, "start" + std::to_string(i)));
            lengths.push_back(Integer{inst.lengths[i]});
            heights.push_back(Integer{inst.heights[i]});
        }
        p.post(Cumulative{starts, lengths, heights, Integer{inst.capacity}}.with_rules(rules).with_proof_mutation(mutation));
        return starts;
    }

    /// The bounds each start is left with once root propagation has run. TTEF
    /// moves bounds rather than reporting conflicts, so this is where it has to
    /// be measured: an enumeration test alone cannot tell whether it fired.
    auto root_bounds(const Instance & inst, CumulativeRules rules, CumulativeProofMutation mutation, const optional<string> & proof_name)
        -> optional<vector<pair<int, int>>>
    {
        Problem p;
        auto starts = post(p, inst, rules, mutation);

        optional<vector<pair<int, int>>> bounds;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               if (! bounds) {
                                   bounds.emplace();
                                   for (const auto & v : starts)
                                       bounds->emplace_back(static_cast<int>(s(v).raw_value), static_cast<int>(s(v).raw_value));
                               }
                               return false;
                           },
                .trace = [&](const CurrentState & s) -> bool {
                    if (! bounds) {
                        bounds.emplace();
                        for (const auto & v : starts)
                            bounds->emplace_back(static_cast<int>(s.lower_bound(v).raw_value), static_cast<int>(s.upper_bound(v).raw_value));
                    }
                    return false;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        return bounds;
    }

    auto fail(const string & message) -> void
    {
        println(cerr, "cumulative energetic: {}", message);
        exit(EXIT_FAILURE);
    }

    /// "starts lo:hi,... / lengths / heights / capacity", so that a fixture
    /// found by --search can be handed straight back in.
    auto parse_instance(const string & spec) -> Instance
    {
        vector<string> parts;
        for (size_t at = 0, next; at <= spec.size(); at = next + 1) {
            next = spec.find('/', at);
            if (next == string::npos)
                next = spec.size();
            parts.push_back(spec.substr(at, next - at));
            if (next == spec.size())
                break;
        }
        if (parts.size() != 4)
            fail("instance spec wants four /-separated parts, got " + std::to_string(parts.size()));

        auto split = [](const string & s) {
            vector<string> out;
            for (size_t at = 0, next; at <= s.size(); at = next + 1) {
                next = s.find(',', at);
                if (next == string::npos)
                    next = s.size();
                out.push_back(s.substr(at, next - at));
                if (next == s.size())
                    break;
            }
            return out;
        };

        Instance inst{{}, {}, {}, std::stoi(parts[3])};
        for (const auto & r : split(parts[0])) {
            auto colon = r.find(':');
            inst.start_ranges.emplace_back(std::stoi(r.substr(0, colon)), std::stoi(r.substr(colon + 1)));
        }
        for (const auto & l : split(parts[1]))
            inst.lengths.push_back(std::stoi(l));
        for (const auto & h : split(parts[2]))
            inst.heights.push_back(std::stoi(h));
        return inst;
    }

    auto show_instance(const Instance & inst) -> string
    {
        string out;
        for (size_t i = 0; i < inst.start_ranges.size(); ++i)
            out += (i ? "," : "") + std::to_string(inst.start_ranges[i].first) + ":" + std::to_string(inst.start_ranges[i].second);
        out += "/";
        for (size_t i = 0; i < inst.lengths.size(); ++i)
            out += (i ? "," : "") + std::to_string(inst.lengths[i]);
        out += "/";
        for (size_t i = 0; i < inst.heights.size(); ++i)
            out += (i ? "," : "") + std::to_string(inst.heights[i]);
        return out + "/" + std::to_string(inst.capacity);
    }

    /// A fixture is only a test of the *claim* if the claim is tight: a push to
    /// v that a solution with the pushed task at v−1 would refute. Where the
    /// push is merely valid, "one too far" is valid too, and VeriPB verifies the
    /// corrupted proof --- which is a fact about the fixture, not about the
    /// rule. So: TTEF must move a bound edge-finding does not, and some solution
    /// must sit exactly on the bound it moves to.
    auto search_for_fixture(
        const CumulativeRules & weaker, const CumulativeRules & stronger, unsigned long long seed_from, unsigned long long candidates) -> void
    {
        std::mt19937 rand(static_cast<unsigned>(seed_from));
        for (unsigned long long attempt = 0; attempt < candidates; ++attempt) {
            auto n = 3 + static_cast<size_t>(rand() % 3);
            auto capacity = 2 + static_cast<int>(rand() % 3);
            Instance inst{{}, {}, {}, capacity};
            for (size_t i = 0; i < n; ++i) {
                auto len = 1 + static_cast<int>(rand() % 5);
                auto lo = static_cast<int>(rand() % 6);
                auto slack = static_cast<int>(rand() % 7);
                inst.start_ranges.emplace_back(lo, lo + slack);
                inst.lengths.push_back(len);
                inst.heights.push_back(1 + static_cast<int>(rand() % capacity));
            }

            auto without = root_bounds(inst, weaker, cumulative_proof_mutation::None{}, nullopt);
            auto with = root_bounds(inst, stronger, cumulative_proof_mutation::None{}, nullopt);
            if (! without || ! with)
                continue;

            set<vector<int>> solutions;
            build_expected(solutions, [&](const vector<int> & starts) { return is_satisfying(inst, starts); }, inst.start_ranges);
            if (solutions.empty())
                continue;

            for (size_t i = 0; i < n; ++i) {
                auto raises = (*with)[i].first > (*without)[i].first;
                auto lowers = (*with)[i].second < (*without)[i].second;
                if (! raises && ! lowers)
                    continue;
                auto landed = raises ? (*with)[i].first : (*with)[i].second;
                auto tight = any_of(solutions, [&](const vector<int> & s) { return s[i] == landed; });
                if (! tight)
                    continue;
                println(cerr, "candidate {} task {} {} -> {} tight, {} solutions", show_instance(inst), i, raises ? "lb" : "ub", landed,
                    solutions.size());
                break;
            }
        }
    }

    /// Every rule setting must find exactly the same solutions: TTEF is a
    /// propagation strength, not a change of constraint. This is the net for an
    /// over-firing push, which removes solutions.
    auto check_enumeration(const string & what, const Instance & inst, CumulativeRules rules, const optional<string> & proof_name) -> void
    {
        print(cerr, "cumulative energetic {} starts={} lens={} hts={} c={}{}", what, inst.start_ranges, inst.lengths, inst.heights, inst.capacity,
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
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    const CumulativeRules ttef{.time_table = true, .overload = true, .profile_overload = true, .edge_finding = true, .time_table_edge_finding = true};
    const CumulativeRules energetic{.time_table = true,
        .overload = true,
        .profile_overload = true,
        .edge_finding = true,
        .time_table_edge_finding = false,
        .energetic_edge_finding = true};

    auto proofs = can_run_veripb();

    // The fixtures, and what it takes to be one. Two things have to hold at
    // once, and hand-picking gets at most one:
    //
    //   * the push must be TIGHT --- some solution must sit exactly on the
    //     bound it lands on. Where the push is merely valid, "one too far" is
    //     valid too and VeriPB verifies the corrupted proof, which is a fact
    //     about the fixture rather than about the rule;
    //   * the non-contained tasks' rows must be LOAD-BEARING. They usually are
    //     not: the guaranteed energy the energetic form adds over TTEF's
    //     profile term is often small enough that the wrapping RUP closes
    //     without it.
    //
    // All three below were found by --search, which generates random instances
    // and keeps the ones where the energetic form moves a bound TTEF does not
    // and a solution sits on it, followed by vetting each candidate against
    // every mutation with an honest control. --describe prints the numbers
    // written down here.
    //
    // Task 1's lower bound moves 3 -> 9, over 5 solutions. The only fixture on
    // which the `capacity` lane bites as well.
    const Instance sharp{{{1, 7}, {3, 9}, {1, 6}, {0, 6}, {1, 5}}, {1, 1, 3, 3, 4}, {3, 3, 1, 2, 3}, 3};

    // Its mirror, where task 0's upper bound falls 3 -> 1 over 2 solutions, so
    // the negated conclusion lands on the guarded row's low guard instead of
    // its high one. Three other bounds move here too, which is what an
    // instance this tight looks like.
    const Instance sharp_mirror{{{0, 3}, {4, 6}, {3, 6}, {2, 7}}, {2, 1, 3, 4}, {2, 3, 2, 3}, 3};

    // A roomier one: task 1's lower bound moves 5 -> 6 over 42 solutions, so
    // the enumeration check below has something to enumerate and the push is
    // still the energetic form's alone.
    const Instance roomy{{{3, 6}, {5, 8}, {2, 6}, {0, 2}}, {2, 5, 2, 1}, {2, 2, 1, 1}, 2};

    // Describe one instance: what edge-finding leaves, what TTEF leaves, and
    // whether the bound it moves to is one a solution sits on. This is how a
    // fixture found by --search gets turned into the numbers written down
    // beside it below.
    for (int a = 1; a < argc; ++a)
        if (string{argv[a]}.starts_with("--describe=")) {
            string arg = argv[a];
            auto inst = parse_instance(arg.substr(arg.find('=') + 1));
            auto without = root_bounds(inst, ttef, cumulative_proof_mutation::None{}, nullopt);
            auto with = root_bounds(inst, energetic, cumulative_proof_mutation::None{}, nullopt);
            if (! without || ! with)
                fail("describe: nothing was reached at the root");
            set<vector<int>> solutions;
            build_expected(solutions, [&](const vector<int> & starts) { return is_satisfying(inst, starts); }, inst.start_ranges);
            println(cerr, "{} solutions {}", show_instance(inst), solutions.size());
            for (size_t i = 0; i < inst.start_ranges.size(); ++i) {
                auto tight = [&](int v) { return any_of(solutions, [&](const vector<int> & s) { return s[i] == v; }); };
                println(cerr, "  task {}: ttef [{}, {}] energetic [{}, {}]{}{}", i, (*without)[i].first, (*without)[i].second, (*with)[i].first,
                    (*with)[i].second, (*with)[i].first > (*without)[i].first ? " lb MOVED" : "",
                    (*with)[i].second < (*without)[i].second ? " ub MOVED" : "");
                println(cerr, "           lb tight {} ub tight {}", tight((*with)[i].first), tight((*with)[i].second));
            }
            return EXIT_SUCCESS;
        }

    // Fixture search: print instances on which TTEF moves a bound
    // edge-finding does not, and moves it somewhere a solution actually sits.
    for (int a = 1; a < argc; ++a)
        if (string{argv[a]} == "--search") {
            unsigned long long from = 1, count = 2000;
            auto number = [&](int at) { return at < argc && argv[at][0] >= '0' && argv[at][0] <= '9'; };
            if (number(a + 1))
                from = std::stoull(argv[a + 1]);
            if (number(a + 2))
                count = std::stoull(argv[a + 2]);
            search_for_fixture(ttef, energetic, from, count);
            return EXIT_SUCCESS;
        }

    // --random: generated instances, each enumerated against a pure C++ oracle
    // and each proof verified. The fixtures above are picked for what they
    // demonstrate; this is the net under them, and it is where a rule that
    // charges a window energy its certificate cannot carry would show up ---
    // the guards on a non-contained task's row come from bounds that move,
    // which no hand-built fixture exercises many of.
    for (int a = 1; a < argc; ++a)
        if (string{argv[a]} == "--random") {
            std::mt19937 rand(a + 1 < argc ? static_cast<unsigned>(std::stoul(argv[a + 1])) : 1u);
            for (auto attempt = 0; attempt < 40; ++attempt) {
                auto n = 3 + static_cast<size_t>(rand() % 3);
                auto capacity = 2 + static_cast<int>(rand() % 3);
                Instance inst{{}, {}, {}, capacity};
                for (size_t i = 0; i < n; ++i) {
                    inst.lengths.push_back(1 + static_cast<int>(rand() % 5));
                    auto lo = static_cast<int>(rand() % 6);
                    inst.start_ranges.emplace_back(lo, lo + static_cast<int>(rand() % 7));
                    inst.heights.push_back(1 + static_cast<int>(rand() % capacity));
                }
                check_enumeration("random " + std::to_string(attempt), inst, energetic,
                    proofs ? make_optional("cumulative_energetic_random_" + std::to_string(attempt)) : nullopt);
            }
            return EXIT_SUCCESS;
        }

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<CumulativeProofMutation> mutation;
        const Instance * fixture = &sharp;
        optional<Instance> from_spec;
        string proof_basename = "cumulative_energetic_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg.starts_with("--instance=")) {
                from_spec = parse_instance(arg.substr(arg.find('=') + 1));
                fixture = &*from_spec;
            }
            else if (arg == "--mutate=none")
                mutation = cumulative_proof_mutation::None{};
            else if (arg == "--mutate=drop_energetic")
                mutation = cumulative_proof_mutation::DropEnergeticContributor{};
            else if (arg == "--mutate=drop")
                mutation = cumulative_proof_mutation::DropContainedTask{};
            else if (arg == "--mutate=toofar")
                mutation = cumulative_proof_mutation::PushOneTooFar{};
            else if (arg == "--mutate=capacity")
                mutation = cumulative_proof_mutation::OmitCapacityLine{};
            else if (arg == "--mutate=mirror_drop_energetic") {
                mutation = cumulative_proof_mutation::DropEnergeticContributor{};
                fixture = &sharp_mirror;
            }
            else if (arg == "--mutate=mirror_toofar") {
                mutation = cumulative_proof_mutation::PushOneTooFar{};
                fixture = &sharp_mirror;
            }
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            auto bounds = root_bounds(*fixture, energetic, *mutation, make_optional(proof_basename));
            // A push deliberately taken one unit past the truth can empty the
            // pushed task's domain at the root, so no node is ever traced ---
            // which is itself evidence the corruption fired, and the proof it
            // wrote is the one veripb has to reject. Every other lane leaves
            // the inference alone, so nothing reached there really would mean
            // an empty proof.
            if (! bounds && ! std::holds_alternative<cumulative_proof_mutation::PushOneTooFar>(*mutation))
                fail("mutation mode: nothing was reached, so the proof is empty");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // The rule fires, pushes exactly as far as the energy supports, and does so
    // where edge-finding on its own does not. `raises` says which bound the
    // fixture is about, and `task` which task it is about.
    for (const auto & [name, inst, task, raises, expected] : vector<tuple<string, Instance, size_t, bool, int>>{
             {"sharp", sharp, 1, true, 9}, {"sharp_mirror", sharp_mirror, 0, false, 1}, {"roomy", roomy, 1, true, 6}}) {
        auto off = root_bounds(inst, ttef, cumulative_proof_mutation::None{}, nullopt);
        auto on = root_bounds(inst, energetic, cumulative_proof_mutation::None{}, proofs ? make_optional("cumulative_energetic_" + name) : nullopt);
        if (! off || ! on)
            fail(name + ": nothing was reached at the root");

        auto pick = [&, task = task, raises = raises](const vector<pair<int, int>> & b) { return raises ? b[task].first : b[task].second; };
        if (raises ? pick(*off) >= expected : pick(*off) <= expected)
            fail(name + ": TTEF alone already reaches the push, so this fixture measures nothing");
        if (pick(*on) != expected)
            fail(name + ": expected the pushed task's bound to reach " + std::to_string(expected) + ", got " + std::to_string(pick(*on)));
        println(cerr, "cumulative energetic {}: task {} {} {} -> {}", name, task, raises ? "lb" : "ub", pick(*off), pick(*on));
        if (proofs)
            verify_proof_and_clean_up("cumulative_energetic_" + name);
    }

    // Alongside the rules that share the sweep and the guarded rows with it.
    // Not-first / not-last reads the same `window_total` and takes the same
    // task's contribution back out of it, so its certificate has to cite the
    // energetic rows too --- a lane worth having, because a rule that quietly
    // cited the contained-task set instead would fire on energy its proof did
    // not carry. The elastic rungs are here because they share the sweep's
    // supply figure and nothing else, and running them together is what would
    // catch a guarded-row cache keyed on too little.
    if (proofs)
        for (const auto & [name, extra] : vector<pair<string, CumulativeRules>>{{"nfnl",
                                                                                    [&] {
                                                                                        auto r = energetic;
                                                                                        r.not_first_not_last = true;
                                                                                        return r;
                                                                                    }()},
                 {"everything", [&] {
                      auto r = energetic;
                      r.not_first_not_last = true;
                      r.elastic_overload = true;
                      r.knapsack_overload = true;
                      return r;
                  }()}}) {
            for (const auto & [what, inst] : vector<pair<string, Instance>>{{"sharp", sharp}, {"sharp_mirror", sharp_mirror}, {"roomy", roomy}}) {
                auto basename = "cumulative_energetic_" + name + "_" + what;
                if (! root_bounds(inst, extra, cumulative_proof_mutation::None{}, make_optional(basename)))
                    fail(name + " " + what + ": nothing was reached at the root");
                verify_proof_and_clean_up(basename);
            }
            println(cerr, "cumulative energetic with {}: certified on every fixture", name);
        }

    // Soundness, over instances small enough to enumerate: the rule may not
    // lose a solution, with or without a proof being written.
    for (const auto & [name, inst] : vector<pair<string, Instance>>{{"sharp", sharp}, {"sharp_mirror", sharp_mirror}, {"roomy", roomy},
             {"tight", Instance{{{0, 3}, {0, 3}, {1, 2}, {0, 5}}, {2, 2, 3, 2}, {1, 1, 1, 1}, 2}},
             {"mixed_heights", Instance{{{0, 4}, {0, 4}, {1, 2}, {0, 6}}, {3, 2, 4, 2}, {2, 1, 1, 2}, 3}}}) {
        check_enumeration(name, inst, energetic, nullopt);
        if (proofs)
            check_enumeration(name, inst, energetic, make_optional("cumulative_energetic_enum_" + name));
    }

    return EXIT_SUCCESS;
}
