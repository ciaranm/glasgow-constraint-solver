#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <climits>
#include <cstdlib>
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

    /// The lower bound each start is left with once root propagation has run,
    /// which is where a pruning rule has to be measured: edge-finding moves
    /// bounds rather than reporting conflicts, so an enumeration test alone
    /// cannot tell whether it fired.
    auto root_lower_bounds(const Instance & inst, CumulativeRules rules, CumulativeProofMutation mutation, const optional<string> & proof_name)
        -> optional<vector<int>>
    {
        Problem p;
        auto starts = post(p, inst, rules, mutation);

        optional<vector<int>> bounds;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               if (! bounds) {
                                   bounds.emplace();
                                   for (const auto & v : starts)
                                       bounds->push_back(static_cast<int>(s(v).raw_value));
                               }
                               return false;
                           },
                .trace = [&](const CurrentState & s) -> bool {
                    if (! bounds) {
                        bounds.emplace();
                        for (const auto & v : starts)
                            bounds->push_back(static_cast<int>(s.lower_bound(v).raw_value));
                    }
                    return false;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        return bounds;
    }

    auto fail(const string & message) -> void
    {
        println(cerr, "cumulative edge finding: {}", message);
        exit(EXIT_FAILURE);
    }

    /// Both rule settings must find exactly the same solutions: edge-finding is
    /// a propagation strength, not a change of constraint. This is the net for
    /// an over-firing push, which removes solutions.
    auto check_enumeration(const string & what, const Instance & inst, CumulativeRules rules, const optional<string> & proof_name) -> void
    {
        print(cerr, "cumulative edge finding {} starts={} lens={} hts={} c={}{}", what, inst.start_ranges, inst.lengths, inst.heights, inst.capacity,
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

    const CumulativeRules without{.time_table = true, .overload = true, .profile_overload = true, .edge_finding = false};
    const CumulativeRules with{.time_table = true, .overload = true, .profile_overload = true, .edge_finding = true};

    auto proofs = can_run_veripb();

    // The fixture the whole file turns on, and it took a randomised search to
    // find the shape: four tasks that exactly fill [0, 8) at capacity two, each
    // with slack enough that its mandatory part is EMPTY. Time-tabling
    // therefore sees nothing at all --- no profile, no blocked time --- so the
    // fifth task's push to 8 can only come from the energy argument.
    //
    // Instances without that slack are worthless here: a narrow start domain
    // gives a task a big mandatory part, time-tabling then makes the same push,
    // and unit propagation over the time-table encoding closes the conclusion's
    // RUP whatever the derivation above it says. 301 randomly generated firings
    // were all of that kind before this family was found.
    const Instance packed{{{0, 4}, {0, 4}, {0, 4}, {0, 4}, {0, 12}}, {4, 4, 4, 4, 4}, {1, 1, 1, 1, 1}, 2};

    // The same, over a window that does not start where the tasks' domains do,
    // so the derivation's lower guard is a real order literal rather than a
    // constant and the citing pol has to discharge it.
    const Instance packed_offset{{{2, 6}, {2, 6}, {2, 6}, {2, 6}, {2, 20}}, {4, 4, 4, 4, 4}, {1, 1, 1, 1, 1}, 2};

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<CumulativeProofMutation> mutation;
        string proof_basename = "cumulative_edge_finding_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=drop")
                mutation = cumulative_proof_mutation::DropContainedTask{};
            else if (arg == "--mutate=toofar")
                mutation = cumulative_proof_mutation::PushOneTooFar{};
            else if (arg == "--mutate=capacity")
                mutation = cumulative_proof_mutation::OmitCapacityLine{};
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            auto bounds = root_lower_bounds(packed_offset, with, *mutation, make_optional(proof_basename));
            if (! bounds)
                fail("mutation mode: nothing was reached, so the proof is empty");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // The rule fires, and pushes exactly as far as the energy supports.
    for (const auto & [name, inst, expected_push] :
        vector<tuple<string, Instance, int>>{{"packed", packed, 8}, {"packed_offset", packed_offset, 10}}) {
        auto off = root_lower_bounds(inst, without, cumulative_proof_mutation::None{}, nullopt);
        auto on =
            root_lower_bounds(inst, with, cumulative_proof_mutation::None{}, proofs ? make_optional("cumulative_edge_finding_" + name) : nullopt);
        if (! off || ! on)
            fail(name + ": nothing was reached at the root");
        if (off->back() >= expected_push)
            fail(name + ": time-tabling alone already reaches the push, so this fixture measures nothing");
        if (on->back() != expected_push)
            fail(name + ": expected the pushed task's lower bound to reach " + std::to_string(expected_push) + ", got " + std::to_string(on->back()));
        println(cerr, "cumulative edge finding {}: pushed task lb {} -> {}", name, off->back(), on->back());
        if (proofs)
            verify_proof_and_clean_up("cumulative_edge_finding_" + name);
    }

    // Soundness, over instances small enough to enumerate: the rule may not
    // lose a solution, with or without a proof being written.
    for (const auto & [name, inst] :
        vector<pair<string, Instance>>{{"packed", packed}, {"tight", Instance{{{0, 3}, {0, 3}, {0, 5}}, {2, 2, 3}, {1, 1, 1}, 2}},
            {"mixed_heights", Instance{{{0, 4}, {0, 4}, {0, 6}}, {3, 2, 2}, {2, 1, 2}, 3}},
            {"unit_lengths", Instance{{{0, 3}, {0, 3}, {0, 3}, {0, 5}}, {1, 1, 1, 2}, {1, 1, 1, 1}, 2}}}) {
        check_enumeration(name, inst, with, nullopt);
        if (proofs)
            check_enumeration(name, inst, with, make_optional("cumulative_edge_finding_enum_" + name));
    }

    return EXIT_SUCCESS;
}
