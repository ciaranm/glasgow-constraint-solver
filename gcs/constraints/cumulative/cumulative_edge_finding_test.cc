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
    // A length and a height are each a range: `{v, v}` is a constant, and
    // `{v, w}` with v < w a decision variable, which the rule counts at `v` ---
    // what the task guarantees. A variable length is what its energy rows carry
    // a guard for; a variable height is what makes a citer convert those rows
    // into contribution terms before they can cancel (#689).
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
        for (size_t i = 0; i < inst.heights.size(); ++i) {
            if (! height_is_var(inst, i))
                heights.push_back(constant_variable(Integer{inst.heights[i].first}));
            else {
                heights.push_back(
                    p.create_integer_variable(Integer{inst.heights[i].first}, Integer{inst.heights[i].second}, "height" + std::to_string(i)));
                posted.all_vars.push_back(heights.back());
            }
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
        p.post(
            Cumulative{posted.starts, lengths, heights, constant_variable(Integer{inst.capacity})}.with_rules(rules).with_proof_mutation(mutation));
        return posted;
    }

    /// The lower bound each start is left with once root propagation has run,
    /// which is where a pruning rule has to be measured: edge-finding moves
    /// bounds rather than reporting conflicts, so an enumeration test alone
    /// cannot tell whether it fired.
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
    const Instance packed{
        {{0, 4}, {0, 4}, {0, 4}, {0, 4}, {0, 12}}, {{4, 4}, {4, 4}, {4, 4}, {4, 4}, {4, 4}}, {{1, 1}, {1, 1}, {1, 1}, {1, 1}, {1, 1}}, 2};

    // The same, over a window that does not start where the tasks' domains do,
    // so the derivation's lower guard is a real order literal rather than a
    // constant and the citing pol has to discharge it.
    const Instance packed_offset{
        {{2, 6}, {2, 6}, {2, 6}, {2, 6}, {2, 20}}, {{4, 4}, {4, 4}, {4, 4}, {4, 4}, {4, 4}}, {{1, 1}, {1, 1}, {1, 1}, {1, 1}, {1, 1}}, 2};

    // The mirror image: [4, 12) is full, and the fifth task ENDS inside it but
    // starts before, so it is its upper bound that has to fall --- to 2, the
    // last start that keeps it clear of the window altogether. Same window,
    // same energy, and the negated conclusion lands on the row's low guard
    // instead of its high one.
    //
    // The pushed task is shorter than the rest on purpose. At length four the
    // push would pin it to its own lower bound, and then the one-too-far
    // mutation empties the domain rather than corrupting a proof.
    const Instance packed_mirror{
        {{4, 8}, {4, 8}, {4, 8}, {4, 8}, {0, 8}}, {{4, 4}, {4, 4}, {4, 4}, {4, 4}, {2, 2}}, {{1, 1}, {1, 1}, {1, 1}, {1, 1}, {1, 1}}, 2};

    // `packed` with one of the four contained tasks given a variable duration.
    // It guarantees the same four units of energy, so the window is as full as
    // before and the push is to the same place --- but the row saying so is now
    // a statement about a length the model does not fix, and carries a guard
    // for it that the citing pol has to discharge (#689).
    const Instance packed_var{
        {{0, 4}, {0, 4}, {0, 4}, {0, 4}, {0, 12}}, {{4, 5}, {4, 4}, {4, 4}, {4, 4}, {4, 4}}, {{1, 1}, {1, 1}, {1, 1}, {1, 1}, {1, 1}}, 2};

    // The other place a length guard turns up: on the *pushed* task's own row,
    // which is cited at the threshold rather than for containment. Its clipped
    // energy is measured at lb(l) like everything else, so the push is again to
    // eight, and it is the length it might have that has to not matter.
    const Instance packed_var_pushed{
        {{0, 4}, {0, 4}, {0, 4}, {0, 4}, {0, 12}}, {{4, 4}, {4, 4}, {4, 4}, {4, 4}, {4, 6}}, {{1, 1}, {1, 1}, {1, 1}, {1, 1}, {1, 1}}, 2};

    // `packed` with one of the four contained tasks given a variable height. It
    // guarantees the same unit of demand, so the window is as full as before and
    // the push is to the same place --- but that task is not in a capacity row
    // as `h x active` at all, so the citing pol has to convert its energy row
    // into contribution terms before anything cancels (#689).
    const Instance packed_var_height{
        {{0, 4}, {0, 4}, {0, 4}, {0, 4}, {0, 12}}, {{4, 4}, {4, 4}, {4, 4}, {4, 4}, {4, 4}}, {{1, 2}, {1, 1}, {1, 1}, {1, 1}, {1, 1}}, 2};

    // And on the *pushed* task, whose row is cited at the threshold rather than
    // for containment, so its own contribution comes back out of the window in
    // the converted form too.
    const Instance packed_var_height_pushed{
        {{0, 4}, {0, 4}, {0, 4}, {0, 4}, {0, 12}}, {{4, 4}, {4, 4}, {4, 4}, {4, 4}, {4, 4}}, {{1, 1}, {1, 1}, {1, 1}, {1, 1}, {1, 2}}, 2};

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    {
        optional<CumulativeProofMutation> mutation;
        const Instance * fixture = &packed_offset;
        string proof_basename = "cumulative_edge_finding_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=drop")
                mutation = cumulative_proof_mutation::DropContainedTask{};
            else if (arg == "--mutate=toofar")
                mutation = cumulative_proof_mutation::PushOneTooFar{};
            else if (arg == "--mutate=capacity")
                mutation = cumulative_proof_mutation::OmitCapacityLine{};
            else if (arg == "--mutate=mirror_toofar") {
                mutation = cumulative_proof_mutation::PushOneTooFar{};
                fixture = &packed_mirror;
            }
            else if (arg == "--mutate=mirror_drop") {
                mutation = cumulative_proof_mutation::DropContainedTask{};
                fixture = &packed_mirror;
            }
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }

        if (mutation) {
            auto bounds = root_bounds(*fixture, with, *mutation, make_optional(proof_basename));
            if (! bounds)
                fail("mutation mode: nothing was reached, so the proof is empty");
            println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    // The rule fires, and pushes exactly as far as the energy supports --- in
    // both directions. `raises` says which bound the fixture is about.
    for (const auto & [name, inst, raises, expected] :
        vector<tuple<string, Instance, bool, int>>{{"packed", packed, true, 8}, {"packed_offset", packed_offset, true, 10},
            {"packed_mirror", packed_mirror, false, 2}, {"packed_var", packed_var, true, 8}, {"packed_var_pushed", packed_var_pushed, true, 8},
            {"packed_var_height", packed_var_height, true, 8}, {"packed_var_height_pushed", packed_var_height_pushed, true, 8}}) {
        auto off = root_bounds(inst, without, cumulative_proof_mutation::None{}, nullopt);
        auto on = root_bounds(inst, with, cumulative_proof_mutation::None{}, proofs ? make_optional("cumulative_edge_finding_" + name) : nullopt);
        if (! off || ! on)
            fail(name + ": nothing was reached at the root");

        auto pick = [&, raises = raises](const vector<pair<int, int>> & b) { return raises ? b.back().first : b.back().second; };
        if (raises ? pick(*off) >= expected : pick(*off) <= expected)
            fail(name + ": time-tabling alone already reaches the push, so this fixture measures nothing");
        if (pick(*on) != expected)
            fail(name + ": expected the pushed task's bound to reach " + std::to_string(expected) + ", got " + std::to_string(pick(*on)));
        println(cerr, "cumulative edge finding {}: pushed task {} {} -> {}", name, raises ? "lb" : "ub", pick(*off), pick(*on));
        if (proofs)
            verify_proof_and_clean_up("cumulative_edge_finding_" + name);
    }

    // Soundness, over instances small enough to enumerate: the rule may not
    // lose a solution, with or without a proof being written.
    for (const auto & [name, inst] : vector<pair<string, Instance>>{{"packed", packed},
             {"tight", Instance{{{0, 3}, {0, 3}, {0, 5}}, {{2, 2}, {2, 2}, {3, 3}}, {{1, 1}, {1, 1}, {1, 1}}, 2}},
             {"mixed_heights", Instance{{{0, 4}, {0, 4}, {0, 6}}, {{3, 3}, {2, 2}, {2, 2}}, {{2, 2}, {1, 1}, {2, 2}}, 3}},
             {"unit_lengths", Instance{{{0, 3}, {0, 3}, {0, 3}, {0, 5}}, {{1, 1}, {1, 1}, {1, 1}, {2, 2}}, {{1, 1}, {1, 1}, {1, 1}, {1, 1}}, 2}},
             {"var_contained", packed_var}, {"var_pushed", packed_var_pushed}, {"var_height_contained", packed_var_height},
             {"var_height_pushed", packed_var_height_pushed}}) {
        check_enumeration(name, inst, with, nullopt);
        if (proofs)
            check_enumeration(name, inst, with, make_optional("cumulative_edge_finding_enum_" + name));
    }

    return EXIT_SUCCESS;
}
