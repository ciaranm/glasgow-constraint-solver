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
        println(cerr, "cumulative ttef: {}", message);
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
    auto search_for_fixture(const CumulativeRules & ef, const CumulativeRules & ttef, unsigned long long seed_from, unsigned long long candidates)
        -> void
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

            auto without = root_bounds(inst, ef, cumulative_proof_mutation::None{}, nullopt);
            auto with = root_bounds(inst, ttef, cumulative_proof_mutation::None{}, nullopt);
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
        print(cerr, "cumulative ttef {} starts={} lens={} hts={} c={}{}", what, inst.start_ranges, inst.lengths, inst.heights, inst.capacity,
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

    const CumulativeRules ef{.time_table = true, .overload = true, .profile_overload = true, .edge_finding = true};
    const CumulativeRules ttef{.time_table = true, .overload = true, .profile_overload = true, .edge_finding = true, .time_table_edge_finding = true};

    auto proofs = can_run_veripb();

    // The fixture, and what it takes to be one. Over [0, 8) at capacity two:
    //
    //   * two contained tasks of length four, each with slack enough that its
    //     mandatory part is EMPTY, so they carry energy but raise no profile;
    //   * a task whose mandatory part [3, 8) lies inside the window but which
    //     is not contained by it, so only the profile term counts it;
    //   * the task to push, which starts inside the window and runs past it.
    //
    // 8 units of contained energy against a supply of 16 leaves edge-finding
    // nothing to say: a length-four unit-height task fits. Add the 5 units of
    // profile and the window holds only 3 more, so the pushed task cannot start
    // before 5. The profile is under capacity everywhere, so time-tabling sees
    // nothing either, and the push is TTEF's alone.
    const Instance profile_push{{{0, 4}, {0, 4}, {2, 3}, {0, 12}}, {4, 4, 6, 4}, {1, 1, 1, 1}, 2};

    // The same instance reflected about t = 16, so the window is [8, 16) and
    // the pushed task ENDS inside it but starts before: its upper bound falls
    // to 7 rather than its lower bound rising to 5. Same energy, same profile,
    // and the negated conclusion lands on the guarded row's low guard instead
    // of its high one.
    const Instance profile_push_mirror{{{8, 12}, {8, 12}, {7, 8}, {0, 12}}, {4, 4, 6, 4}, {1, 1, 1, 1}, 2};

    // The fixture that best *demonstrates* the rule is not the one that makes a
    // mutation bite, and neither of the two above makes any of them bite. Two
    // things have to hold at once, and hand-picking gets at most one:
    //
    //   * the push must be TIGHT --- some solution must sit exactly on the
    //     bound it lands on. Where the push is merely valid, "one too far" is
    //     valid too and VeriPB verifies the corrupted proof, which is a fact
    //     about the fixture rather than about the rule;
    //   * the pins must be LOAD-BEARING. They usually are not: the pol leaves
    //     the non-contained tasks' activity terms uncancelled, unit propagation
    //     assigns them from the reason's own bound literals, and the wrapping
    //     RUP closes without them. Dropping every pin is rejected on 13 of 248
    //     searched instances; dropping one, on fewer still.
    //
    // Both were found by --search, which generates random instances and keeps
    // the ones where TTEF moves a bound edge-finding does not and a solution
    // sits on it, followed by vetting each candidate against every mutation
    // with an honest control. --describe prints the numbers written down here.
    //
    // Task 2's lower bound moves 5 -> 6, over 30 solutions.
    const Instance sharp{{{0, 3}, {5, 6}, {5, 7}, {2, 4}}, {3, 1, 3, 5}, {1, 1, 1, 2}, 3};

    // And its mirror, where task 0's upper bound falls 5 -> 4 over 28
    // solutions, so the negated conclusion lands on the low guard instead.
    const Instance sharp_mirror{{{1, 5}, {2, 5}, {5, 6}}, {2, 5, 1}, {3, 1, 1}, 4};

    // Describe one instance: what edge-finding leaves, what TTEF leaves, and
    // whether the bound it moves to is one a solution sits on. This is how a
    // fixture found by --search gets turned into the numbers written down
    // beside it below.
    for (int a = 1; a < argc; ++a)
        if (string{argv[a]}.starts_with("--describe=")) {
            string arg = argv[a];
            auto inst = parse_instance(arg.substr(arg.find('=') + 1));
            auto without = root_bounds(inst, ef, cumulative_proof_mutation::None{}, nullopt);
            auto with = root_bounds(inst, ttef, cumulative_proof_mutation::None{}, nullopt);
            if (! without || ! with)
                fail("describe: nothing was reached at the root");
            set<vector<int>> solutions;
            build_expected(solutions, [&](const vector<int> & starts) { return is_satisfying(inst, starts); }, inst.start_ranges);
            println(cerr, "{} solutions {}", show_instance(inst), solutions.size());
            for (size_t i = 0; i < inst.start_ranges.size(); ++i) {
                auto tight = [&](int v) { return any_of(solutions, [&](const vector<int> & s) { return s[i] == v; }); };
                println(cerr, "  task {}: ef [{}, {}] ttef [{}, {}]{}{}", i, (*without)[i].first, (*without)[i].second, (*with)[i].first,
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
            search_for_fixture(ef, ttef, from, count);
            return EXIT_SUCCESS;
        }

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<CumulativeProofMutation> mutation;
        const Instance * fixture = &sharp;
        optional<Instance> from_spec;
        string proof_basename = "cumulative_ttef_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg.starts_with("--instance=")) {
                from_spec = parse_instance(arg.substr(arg.find('=') + 1));
                fixture = &*from_spec;
            }
            else if (arg == "--mutate=none")
                mutation = cumulative_proof_mutation::None{};
            else if (arg == "--mutate=pin")
                mutation = cumulative_proof_mutation::DropProfilePin{};
            else if (arg == "--mutate=pins")
                mutation = cumulative_proof_mutation::DropProfilePins{};
            else if (arg == "--mutate=drop")
                mutation = cumulative_proof_mutation::DropContainedTask{};
            else if (arg == "--mutate=toofar")
                mutation = cumulative_proof_mutation::PushOneTooFar{};
            else if (arg == "--mutate=capacity")
                mutation = cumulative_proof_mutation::OmitCapacityLine{};
            else if (arg == "--mutate=mirror_pins") {
                mutation = cumulative_proof_mutation::DropProfilePins{};
                fixture = &sharp_mirror;
            }
            else if (arg == "--mutate=mirror_pin") {
                mutation = cumulative_proof_mutation::DropProfilePin{};
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
            auto bounds = root_bounds(*fixture, ttef, *mutation, make_optional(proof_basename));
            if (! bounds)
                fail("mutation mode: nothing was reached, so the proof is empty");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // The rule fires, pushes exactly as far as the energy supports, and does so
    // where edge-finding on its own does not. `raises` says which bound the
    // fixture is about, and `task` which task it is about.
    for (const auto & [name, inst, task, raises, expected] :
        vector<tuple<string, Instance, size_t, bool, int>>{{"profile_push", profile_push, 3, true, 5},
            {"profile_push_mirror", profile_push_mirror, 3, false, 7}, {"sharp", sharp, 2, true, 6}, {"sharp_mirror", sharp_mirror, 0, false, 4}}) {
        auto off = root_bounds(inst, ef, cumulative_proof_mutation::None{}, nullopt);
        auto on = root_bounds(inst, ttef, cumulative_proof_mutation::None{}, proofs ? make_optional("cumulative_ttef_" + name) : nullopt);
        if (! off || ! on)
            fail(name + ": nothing was reached at the root");

        auto pick = [&, task = task, raises = raises](const vector<pair<int, int>> & b) { return raises ? b[task].first : b[task].second; };
        if (raises ? pick(*off) >= expected : pick(*off) <= expected)
            fail(name + ": edge-finding alone already reaches the push, so this fixture measures nothing");
        if (pick(*on) != expected)
            fail(name + ": expected the pushed task's bound to reach " + std::to_string(expected) + ", got " + std::to_string(pick(*on)));
        println(cerr, "cumulative ttef {}: task {} {} {} -> {}", name, task, raises ? "lb" : "ub", pick(*off), pick(*on));
        if (proofs)
            verify_proof_and_clean_up("cumulative_ttef_" + name);
    }

    // Soundness, over instances small enough to enumerate: the rule may not
    // lose a solution, with or without a proof being written.
    for (const auto & [name, inst] : vector<pair<string, Instance>>{{"profile_push", profile_push}, {"profile_push_mirror", profile_push_mirror},
             {"sharp", sharp}, {"sharp_mirror", sharp_mirror}, {"tight", Instance{{{0, 3}, {0, 3}, {1, 2}, {0, 5}}, {2, 2, 3, 2}, {1, 1, 1, 1}, 2}},
             {"mixed_heights", Instance{{{0, 4}, {0, 4}, {1, 2}, {0, 6}}, {3, 2, 4, 2}, {2, 1, 1, 2}, 3}}}) {
        check_enumeration(name, inst, ttef, nullopt);
        if (proofs)
            check_enumeration(name, inst, ttef, make_optional("cumulative_ttef_enum_" + name));
    }

    return EXIT_SUCCESS;
}
