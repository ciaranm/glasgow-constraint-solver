/* The published not-first / not-last detection for Cumulative, and its
 * certificate (#746).
 *
 * `cumulative_nfnl_test.cc` covers the detection the guarded window-energy
 * lemma can derive. This one covers the rule as Schutt & Wolf and Kameugne et
 * al. state it, which charges the pushed task's overlap at *one end* of the
 * negated conclusion's start range and argues over the contained set's own
 * window rather than the swept one. The two are incomparable, so neither
 * test's fixtures serve the other.
 *
 * The certificate is not a window-energy one at all. It is contiguity: every
 * task in Omega has `ect_k >= ECT(Omega)`, so one running in the prefix is
 * still running at the end of it, and the capacity row at that one time point
 * --- where the pushed task is running too --- caps the whole prefix at
 * `C - c_j`. `drop_contiguity` and `drop_pin` are the mutation lanes aimed at
 * exactly that, and are what a lane inherited from the window-energy rule
 * could not test.
 *
 * Where `ect_j >= ECT(Omega)` one pol does the whole rule. Where it does not,
 * no single time point is where both the contained set and the pushed task are
 * running, and the derivation becomes a chain that walks the bound up `p_j` at
 * a time. Both are fixtured.
 *
 * Lengths and heights are ranges here rather than constants, because over a
 * variable length this is a *different* derivation and not a wider one: `after`
 * is then reified on `s + l` rather than on `s`, and not-last's contiguity rows
 * run backwards over it, which is what #778 was. Everything this rule had ever
 * been run against gave it constants.
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
    // A length and a height are each a range: `{v, v}` is a constant, and
    // `{v, w}` with v < w a decision variable, which the rule counts at `v` ---
    // what the task guarantees. A variable length is what a mode gives this
    // rule and what nothing else here did (#778): the contiguity rows are then
    // stated over `s_k + l_k` rather than over `s_k` alone, which is a
    // different derivation and not merely a wider one.
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
    // them: the starts, then the variable lengths and then the variable
    // heights, each in task order.
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

    /// What posting an instance created: the starts, which is what the bound
    /// measurements read, and every decision variable, which is what an
    /// enumeration has to be told about.
    struct Posted
    {
        vector<IntegerVariableID> starts, all_vars;
    };

    auto post(Problem & p, const Instance & inst, CumulativeRules rules, CumulativeProofMutation mutation = cumulative_proof_mutation::None{})
        -> Posted
    {
        Posted posted;
        vector<IntegerVariableID> lengths, heights;
        for (size_t i = 0; i < inst.start_ranges.size(); ++i) {
            posted.starts.push_back(
                p.create_integer_variable(Integer{inst.start_ranges[i].first}, Integer{inst.start_ranges[i].second}, "start" + std::to_string(i)));
            posted.all_vars.push_back(posted.starts.back());
        }
        for (size_t i = 0; i < inst.lengths.size(); ++i) {
            if (! length_is_var(inst, i))
                lengths.push_back(constant_variable(Integer{inst.lengths[i].first}));
            else {
                lengths.push_back(
                    p.create_integer_variable(Integer{inst.lengths[i].first}, Integer{inst.lengths[i].second}, "length" + std::to_string(i)));
                posted.all_vars.push_back(lengths.back());
            }
        }
        for (size_t i = 0; i < inst.heights.size(); ++i) {
            if (! height_is_var(inst, i))
                heights.push_back(constant_variable(Integer{inst.heights[i].first}));
            else {
                heights.push_back(
                    p.create_integer_variable(Integer{inst.heights[i].first}, Integer{inst.heights[i].second}, "height" + std::to_string(i)));
                posted.all_vars.push_back(heights.back());
            }
        }
        p.post(
            Cumulative{posted.starts, lengths, heights, constant_variable(Integer{inst.capacity})}.with_rules(rules).with_proof_mutation(mutation));
        return posted;
    }

    /// The bounds each start is left with once root propagation has run. TTEF
    /// moves bounds rather than reporting conflicts, so this is where it has to
    /// be measured: an enumeration test alone cannot tell whether it fired.
    auto root_bounds(const Instance & inst, CumulativeRules rules, CumulativeProofMutation mutation, const optional<string> & proof_name)
        -> optional<vector<pair<int, int>>>
    {
        Problem p;
        auto starts = post(p, inst, rules, mutation).starts;

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
        println(cerr, "cumulative published nfnl: {}", message);
        exit(EXIT_FAILURE);
    }

    /// "starts lo:hi,... / lengths / heights / capacity", so that a fixture
    /// found by --search can be handed straight back in. A length or a height
    /// is `v` for a constant and `lo:hi` for a variable one, so the specs
    /// written before this rule was given variable arguments still parse.
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

        auto range = [](const string & r) {
            auto colon = r.find(':');
            if (colon == string::npos)
                return pair<int, int>{std::stoi(r), std::stoi(r)};
            return pair<int, int>{std::stoi(r.substr(0, colon)), std::stoi(r.substr(colon + 1))};
        };

        Instance inst{{}, {}, {}, std::stoi(parts[3])};
        for (const auto & r : split(parts[0]))
            inst.start_ranges.push_back(range(r));
        for (const auto & l : split(parts[1]))
            inst.lengths.push_back(range(l));
        for (const auto & h : split(parts[2]))
            inst.heights.push_back(range(h));
        return inst;
    }

    auto show_instance(const Instance & inst) -> string
    {
        auto show = [](const pair<int, int> & r) {
            return r.first == r.second ? std::to_string(r.first) : std::to_string(r.first) + ":" + std::to_string(r.second);
        };

        string out;
        for (size_t i = 0; i < inst.start_ranges.size(); ++i)
            out += (i ? "," : "") + std::to_string(inst.start_ranges[i].first) + ":" + std::to_string(inst.start_ranges[i].second);
        out += "/";
        for (size_t i = 0; i < inst.lengths.size(); ++i)
            out += (i ? "," : "") + show(inst.lengths[i]);
        out += "/";
        for (size_t i = 0; i < inst.heights.size(); ++i)
            out += (i ? "," : "") + show(inst.heights[i]);
        return out + "/" + std::to_string(inst.capacity);
    }

    /// A fixture is only a test of the *claim* if the claim is tight: a push to
    /// v that a solution with the pushed task at v−1 would refute. Where the
    /// push is merely valid, "one too far" is valid too, and VeriPB verifies the
    /// corrupted proof --- which is a fact about the fixture, not about the
    /// rule. So: TTEF must move a bound edge-finding does not, and some solution
    /// must sit exactly on the bound it moves to.
    auto search_for_fixture(const CumulativeRules & without_rule, const CumulativeRules & with_rule, unsigned long long seed_from,
        unsigned long long candidates, bool variable_arguments) -> void
    {
        std::mt19937 rand(static_cast<unsigned>(seed_from));
        for (unsigned long long attempt = 0; attempt < candidates; ++attempt) {
            auto n = 3 + static_cast<size_t>(rand() % 3);
            auto capacity = 2 + static_cast<int>(rand() % 3);
            Instance inst{{}, {}, {}, capacity};
            for (size_t i = 0; i < n; ++i) {
                auto len = 1 + static_cast<int>(rand() % 5);
                auto height = 1 + static_cast<int>(rand() % capacity);
                auto lo = static_cast<int>(rand() % 6);
                auto slack = static_cast<int>(rand() % 7);
                inst.start_ranges.emplace_back(lo, lo + slack);
                inst.lengths.emplace_back(len, len + (variable_arguments ? static_cast<int>(rand() % 3) : 0));
                inst.heights.emplace_back(height, min(capacity, height + (variable_arguments ? static_cast<int>(rand() % 3) : 0)));
            }

            auto without = root_bounds(inst, without_rule, cumulative_proof_mutation::None{}, nullopt);
            auto with = root_bounds(inst, with_rule, cumulative_proof_mutation::None{}, nullopt);
            if (! without || ! with)
                continue;

            set<vector<int>> solutions;
            build_expected(solutions, [&](const vector<int> & vals) { return is_satisfying(inst, vals); }, all_ranges(inst));
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
        print(cerr, "cumulative published nfnl {} starts={} lens={} hts={} c={}{}", what, inst.start_ranges, inst.lengths, inst.heights,
            inst.capacity, proof_name ? " with proofs:" : ":");
        cerr << flush;

        set<vector<int>> expected, actual;
        build_expected(expected, [&](const vector<int> & vals) { return is_satisfying(inst, vals); }, all_ranges(inst));
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto all_vars = post(p, inst, rules).all_vars;
        solve_for_tests(p, proof_name, actual, tuple{all_vars});
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // The baseline is everything else that is certified, so a fixture here has
    // to show not-first / not-last inferring something time-tabling, the
    // overload check, edge-finding and TTEF together do not.
    const CumulativeRules without_rule{
        .time_table = true, .overload = true, .profile_overload = true, .edge_finding = true, .time_table_edge_finding = true};
    const CumulativeRules with_rule{.time_table = true,
        .overload = true,
        .profile_overload = true,
        .edge_finding = true,
        .time_table_edge_finding = true,
        .not_first_not_last = true,
        .not_first_not_last_published = true};

    auto proofs = can_run_veripb();

    // What a fixture here has to do, and why hand-building one does not work.
    //
    // Not-first / not-last only ever adds an inference on a task that SPANS the
    // window: where a task has one end inside, edge-finding's threshold is the
    // furthest an energy argument over that window can reach, so its push
    // subsumes this rule's and the live-bound test drops the duplicate. A
    // fixture therefore needs a spanning task whose guaranteed energy, once its
    // start is restricted to one side of the contained set's `min ect` or
    // `max lst`, is enough to overflow a window that does not otherwise
    // overflow --- while the contained tasks keep mandatory parts small enough
    // that time-tabling sees nothing. Two hand-built attempts had time-tabling
    // making the same push on its own.
    //
    // And the push has to be TIGHT --- some solution must sit exactly on the
    // bound --- or "one too far" is valid too and VeriPB verifies the corrupted
    // proof. Both were found by --search, which keeps random instances where
    // the rule moves a bound the other rules do not and a solution sits on it,
    // then vetted against every mutation with an honest control. --describe
    // prints the numbers written down here.
    //
    // Capacity three, four tasks. Task 0's lower bound rises 5 -> 6, over 6
    // solutions, and the push is the published detection's alone: everything
    // else certified --- time-tabling, the overload check, edge-finding and
    // TTEF --- leaves it at 5.
    const Instance sharp{{{2, 7}, {1, 5}, {4, 6}, {5, 7}}, {{5, 5}, {4, 4}, {1, 1}, {2, 2}}, {{2, 2}, {2, 2}, {3, 3}, {1, 1}}, 3};

    // The mirror, where task 0's upper bound falls 5 -> 1 over 2 solutions, so
    // the argument runs backwards: the contained set's activity is monotone
    // *down* from `max lst` rather than up to `min ect`, and it is the pushed
    // task's own upper bound rather than its lower one that puts it beside them.
    const Instance sharp_mirror{{{1, 5}, {3, 9}, {3, 6}}, {{5, 5}, {3, 3}, {2, 2}}, {{3, 3}, {2, 2}, {2, 2}}, 3};

    // A roomier one, 20 solutions, so the enumeration check has something to
    // enumerate. Task 1's upper bound falls 6 -> 4.
    const Instance roomy{{{1, 4}, {0, 6}, {1, 7}}, {{1, 1}, {3, 3}, {5, 5}}, {{1, 1}, {2, 2}, {2, 2}}, 2};

    // Describe one instance: what edge-finding leaves, what TTEF leaves, and
    // whether the bound it moves to is one a solution sits on. This is how a
    // fixture found by --search gets turned into the numbers written down
    // beside it below.
    for (int a = 1; a < argc; ++a)
        if (string{argv[a]}.starts_with("--describe=")) {
            string arg = argv[a];
            auto inst = parse_instance(arg.substr(arg.find('=') + 1));
            auto without = root_bounds(inst, without_rule, cumulative_proof_mutation::None{}, nullopt);
            auto with = root_bounds(inst, with_rule, cumulative_proof_mutation::None{}, nullopt);
            if (! without || ! with)
                fail("describe: nothing was reached at the root");
            set<vector<int>> solutions;
            build_expected(solutions, [&](const vector<int> & vals) { return is_satisfying(inst, vals); }, all_ranges(inst));
            println(cerr, "{} solutions {}", show_instance(inst), solutions.size());
            for (size_t i = 0; i < inst.start_ranges.size(); ++i) {
                auto tight = [&](int v) { return any_of(solutions, [&](const vector<int> & s) { return s[i] == v; }); };
                println(cerr, "  task {}: without_rule [{}, {}] with_rule [{}, {}]{}{}", i, (*without)[i].first, (*without)[i].second,
                    (*with)[i].first, (*with)[i].second, (*with)[i].first > (*without)[i].first ? " lb MOVED" : "",
                    (*with)[i].second < (*without)[i].second ? " ub MOVED" : "");
                println(cerr, "           lb tight {} ub tight {}", tight((*with)[i].first), tight((*with)[i].second));
            }
            return EXIT_SUCCESS;
        }

    // Replay one instance spec end to end: enumerate it against the oracle and
    // verify its proof. This is how an instance --random-var stopped on gets
    // shrunk into a fixture small enough to write down here.
    for (int a = 1; a < argc; ++a)
        if (string{argv[a]}.starts_with("--enumerate=")) {
            string arg = argv[a];
            auto inst = parse_instance(arg.substr(arg.find('=') + 1));
            check_enumeration("enumerate", inst, with_rule, proofs ? make_optional("cumulative_published_nfnl_enumerate") : nullopt);
            return EXIT_SUCCESS;
        }

    // Fixture search: print instances on which the rule moves a bound
    // edge-finding does not, and moves it somewhere a solution actually sits.
    // `--search-var` is the same draw with variable lengths and heights, for a
    // fixture that wants the rule to move a bound over one. (The
    // `variable_length` fixture below is not one of those: it came from
    // `--random-var` and `--enumerate`, because what it demonstrates fires
    // below the root rather than at it.)
    for (int a = 1; a < argc; ++a)
        if (string{argv[a]} == "--search" || string{argv[a]} == "--search-var") {
            unsigned long long from = 1, count = 2000;
            auto number = [&](int at) { return at < argc && argv[at][0] >= '0' && argv[at][0] <= '9'; };
            if (number(a + 1))
                from = std::stoull(argv[a + 1]);
            if (number(a + 2))
                count = std::stoull(argv[a + 2]);
            search_for_fixture(without_rule, with_rule, from, count, string{argv[a]} == "--search-var");
            return EXIT_SUCCESS;
        }

    // --random: generated instances, each enumerated against a pure C++ oracle
    // and each proof verified. The fixtures below are picked for what they
    // demonstrate; this is the net under them, and it is where the chain would
    // show up --- a rung walking past the pushed task's own domain is not
    // something a hand-built fixture reaches, and was a real bug this lane
    // found.
    //
    // --random-var is the same net with variable lengths and heights drawn as
    // well. It is a separate mode rather than a widening of the draw above,
    // because the constant-argument sequence is the one that found that bug and
    // is worth keeping exactly as it is. Variable arguments are a different
    // derivation and not a wider one: `after` is then reified on `s + l` rather
    // than on `s` alone, which is what #778 was.
    for (int a = 1; a < argc; ++a)
        if (string{argv[a]} == "--random" || string{argv[a]} == "--random-var") {
            auto variable_arguments = string{argv[a]} == "--random-var";
            std::mt19937 rand(a + 1 < argc ? static_cast<unsigned>(std::stoul(argv[a + 1])) : 1u);
            for (auto attempt = 0; attempt < 40; ++attempt) {
                auto n = 3 + static_cast<size_t>(rand() % 4);
                auto capacity = 2 + static_cast<int>(rand() % 4);
                Instance inst{{}, {}, {}, capacity};
                for (size_t i = 0; i < n; ++i) {
                    auto len = 1 + static_cast<int>(rand() % 6);
                    inst.lengths.emplace_back(len, len + (variable_arguments ? static_cast<int>(rand() % 3) : 0));
                    auto lo = static_cast<int>(rand() % 8);
                    inst.start_ranges.emplace_back(lo, lo + static_cast<int>(rand() % 8));
                    auto height = 1 + static_cast<int>(rand() % capacity);
                    inst.heights.emplace_back(height, min(capacity, height + (variable_arguments ? static_cast<int>(rand() % 3) : 0)));
                }
                // A distinct basename per mode: ctest runs its lanes in one
                // working directory and in parallel, so two lanes writing
                // `..._random_5.pbp` would be reading each other's proof.
                auto basename = string{variable_arguments ? "cumulative_published_nfnl_random_var_" : "cumulative_published_nfnl_random_"};
                check_enumeration(string{variable_arguments ? "random var " : "random "} + std::to_string(attempt), inst, with_rule,
                    proofs ? make_optional(basename + std::to_string(attempt)) : nullopt);
            }
            return EXIT_SUCCESS;
        }

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<CumulativeProofMutation> mutation;
        const Instance * fixture = &sharp;
        optional<Instance> from_spec;
        string proof_basename = "cumulative_published_nfnl_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg.starts_with("--instance=")) {
                from_spec = parse_instance(arg.substr(arg.find('=') + 1));
                fixture = &*from_spec;
            }
            else if (arg == "--mutate=none")
                mutation = cumulative_proof_mutation::None{};
            else if (arg == "--mutate=emit_nothing")
                mutation = cumulative_proof_mutation::PublishedEmitNothing{};
            else if (arg == "--mutate=drop_pin")
                mutation = cumulative_proof_mutation::DropPublishedPin{};
            else if (arg == "--mutate=drop")
                mutation = cumulative_proof_mutation::DropContainedTask{};
            else if (arg == "--mutate=toofar")
                mutation = cumulative_proof_mutation::PushOneTooFar{};
            else if (arg == "--mutate=capacity")
                mutation = cumulative_proof_mutation::OmitCapacityLine{};
            else if (arg == "--mutate=roomy_toofar") {
                mutation = cumulative_proof_mutation::PushOneTooFar{};
                fixture = &roomy;
            }
            else if (arg == "--mutate=roomy_drop_pin") {
                mutation = cumulative_proof_mutation::DropPublishedPin{};
                fixture = &roomy;
            }
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            auto bounds = root_bounds(*fixture, with_rule, *mutation, make_optional(proof_basename));
            // Unlike the other two mutation harnesses, this one does not insist
            // that the root was reached. A push corrupted one step too far can
            // empty a domain outright, and then there is no root to report ---
            // but the proof of that emptying is exactly the corrupted step, and
            // veripb is the thing that judges it. Where a mutation is instead a
            // no-op, the root *is* reached, veripb accepts, and the lane fails,
            // which is the verdict wanted either way.
            if (! bounds)
                println(cerr, "the corrupted inference left nothing at the root, which is itself the corruption");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // The rule fires, pushes exactly as far as the energy supports, and does so
    // where edge-finding on its own does not. `raises` says which bound the
    // fixture is about, and `task` which task it is about.
    for (const auto & [name, inst, task, raises, expected] : vector<tuple<string, Instance, size_t, bool, int>>{
             {"sharp", sharp, 0, true, 6}, {"sharp_mirror", sharp_mirror, 0, false, 1}, {"roomy", roomy, 1, false, 4}}) {
        auto off = root_bounds(inst, without_rule, cumulative_proof_mutation::None{}, nullopt);
        auto on =
            root_bounds(inst, with_rule, cumulative_proof_mutation::None{}, proofs ? make_optional("cumulative_published_nfnl_" + name) : nullopt);
        if (! off || ! on)
            fail(name + ": nothing was reached at the root");

        auto pick = [&, task = task, raises = raises](const vector<pair<int, int>> & b) { return raises ? b[task].first : b[task].second; };
        if (raises ? pick(*off) >= expected : pick(*off) <= expected)
            fail(name + ": edge-finding alone already reaches the push, so this fixture measures nothing");
        if (pick(*on) != expected)
            fail(name + ": expected the pushed task's bound to reach " + std::to_string(expected) + ", got " + std::to_string(pick(*on)));
        println(cerr, "cumulative published nfnl {}: task {} {} {} -> {}", name, task, raises ? "lb" : "ub", pick(*off), pick(*on));
        if (proofs)
            verify_proof_and_clean_up("cumulative_published_nfnl_" + name);
    }

    // Soundness, over instances small enough to enumerate: the rule may not
    // lose a solution, with or without a proof being written.
    for (const auto & [name, inst] : vector<pair<string, Instance>>{{"sharp", sharp}, {"sharp_mirror", sharp_mirror}, {"roomy", roomy},
             {"tight", Instance{{{0, 3}, {0, 3}, {1, 2}, {0, 5}}, {{2, 2}, {2, 2}, {3, 3}, {2, 2}}, {{1, 1}, {1, 1}, {1, 1}, {1, 1}}, 2}},
             {"mixed_heights", Instance{{{0, 4}, {0, 4}, {1, 2}, {0, 6}}, {{3, 3}, {2, 2}, {4, 4}, {2, 2}}, {{2, 2}, {1, 1}, {1, 1}, {2, 2}}, 3}},
             // #778: task 0's length is a decision variable, so its `after`
             // flags are reified on `s_0 + l_0` and not on `s_0`. Not-last's
             // contiguity rows run backwards --- `active at u` implies `active
             // at v` for u > v --- and over a sum unit propagation cannot see
             // that for itself, so the row needs the bridge that cancels the
             // sum. Without it veripb rejects one, on every seed tried: the
             // rule fires below the root here rather than at it, so this is an
             // enumeration fixture and not a bound-measurement one.
             {"variable_length", Instance{{{3, 4}, {4, 4}, {2, 6}}, {{2, 4}, {4, 4}, {1, 1}}, {{1, 1}, {2, 2}, {3, 3}}, 3}}}) {
        check_enumeration(name, inst, with_rule, nullopt);
        if (proofs)
            check_enumeration(name, inst, with_rule, make_optional("cumulative_published_nfnl_enum_" + name));
    }

    return EXIT_SUCCESS;
}
