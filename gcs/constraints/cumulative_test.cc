#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <climits>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <set>
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
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::tuple;
using std::uniform_int_distribution;
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
    auto run_cumulative_test(bool proofs, const ViewWrapConfig & view_cfg, const vector<pair<int, int>> & start_ranges,
        const vector<int> & lengths, const vector<int> & heights, int capacity) -> void
    {
        auto wraps = wraps_for_positions(view_cfg, static_cast<int>(start_ranges.size()));
        print(cerr, "cumulative [{}] {} {} {} c={}{}", view_wrap_config_label(view_cfg),
            start_ranges, lengths, heights, capacity, proofs ? " with proofs:" : ":");
        cerr << flush;

        auto n = start_ranges.size();

        auto is_satisfying = [&](const vector<int> & starts) {
            int t_lo = INT_MAX, t_hi = INT_MIN;
            for (size_t i = 0; i < n; ++i) {
                if (lengths[i] == 0 || heights[i] == 0)
                    continue;
                t_lo = min(t_lo, starts[i]);
                t_hi = max(t_hi, starts[i] + lengths[i] - 1);
            }
            for (int t = t_lo; t <= t_hi; ++t) {
                int load = 0;
                for (size_t i = 0; i < n; ++i)
                    if (starts[i] <= t && t < starts[i] + lengths[i])
                        load += heights[i];
                if (load > capacity)
                    return false;
            }
            return true;
        };

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, start_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> starts;
        for (size_t i = 0; i < start_ranges.size(); ++i)
            starts.push_back(create_integer_variable_or_constant_with_view(p, start_ranges.at(i), wraps.at(i)));

        vector<Integer> lengths_i, heights_i;
        for (auto l : lengths)
            lengths_i.push_back(Integer{l});
        for (auto h : heights)
            heights_i.push_back(Integer{h});

        p.post(Cumulative{starts, lengths_i, heights_i, Integer{capacity}});

        auto proof_name = proofs ? make_optional("cumulative_test_" + view_wrap_config_label(view_cfg)) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{starts});

        check_results(proof_name, expected, actual);
    }
}

namespace
{
    // Dup-variable test: Cumulative with the same start handle for two
    // tasks. The two tasks share a start time, so their heights add at
    // every time point inside their (possibly different) durations.
    // Consistency isn't checked on dup runs; see tmp/duplicate_var_audit.md.
    auto run_dup_cumulative_test(bool proofs,
        const vector<pair<int, int>> & unique_start_ranges,
        const vector<int> & positions,
        const vector<int> & lengths, const vector<int> & heights, int capacity) -> void
    {
        print(cerr, "cumulative dup unique_starts={} positions={} lens={} hts={} c={}{}",
            unique_start_ranges, positions, lengths, heights, capacity,
            proofs ? " with proofs:" : ":");
        cerr << flush;

        auto n = positions.size();

        auto is_satisfying = [&](const vector<int> & unique_starts) {
            int t_lo = INT_MAX, t_hi = INT_MIN;
            for (size_t i = 0; i < n; ++i) {
                if (lengths[i] == 0 || heights[i] == 0)
                    continue;
                int s = unique_starts.at(positions.at(i));
                t_lo = min(t_lo, s);
                t_hi = max(t_hi, s + lengths[i] - 1);
            }
            for (int t = t_lo; t <= t_hi; ++t) {
                int load = 0;
                for (size_t i = 0; i < n; ++i) {
                    int s = unique_starts.at(positions.at(i));
                    if (s <= t && t < s + lengths[i])
                        load += heights[i];
                }
                if (load > capacity)
                    return false;
            }
            return true;
        };

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, unique_start_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> unique_starts;
        for (auto & [lo, hi] : unique_start_ranges)
            unique_starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        vector<IntegerVariableID> starts;
        for (auto pos : positions)
            starts.push_back(unique_starts.at(pos));

        vector<Integer> lengths_i, heights_i;
        for (auto l : lengths)
            lengths_i.push_back(Integer{l});
        for (auto h : heights)
            heights_i.push_back(Integer{h});

        p.post(Cumulative{starts, lengths_i, heights_i, Integer{capacity}});

        auto proof_name = proofs ? make_optional("cumulative_test_dup") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{unique_starts});
        check_results(proof_name, expected, actual);
    }
}

namespace
{
    // Variable-capacity test: the capacity is a decision variable. The
    // capacity value is enumerated alongside the starts (appended as the
    // last element of every solution vector), and the satisfiability check
    // reads it from there. Lengths and heights stay constant.
    auto run_cumulative_var_cap_test(bool proofs, const std::string & tag,
        const vector<pair<int, int>> & start_ranges,
        const vector<int> & lengths, const vector<int> & heights, pair<int, int> cap_range) -> void
    {
        print(cerr, "cumulative varcap {} starts={} lens={} hts={} cap=[{},{}]{}",
            tag, start_ranges, lengths, heights, cap_range.first, cap_range.second,
            proofs ? " with proofs:" : ":");
        cerr << flush;

        auto n = start_ranges.size();

        auto is_satisfying = [&](const vector<int> & vals) {
            int capacity = vals.at(n);
            int t_lo = INT_MAX, t_hi = INT_MIN;
            for (size_t i = 0; i < n; ++i) {
                if (lengths[i] == 0 || heights[i] == 0)
                    continue;
                t_lo = min(t_lo, vals[i]);
                t_hi = max(t_hi, vals[i] + lengths[i] - 1);
            }
            for (int t = t_lo; t <= t_hi; ++t) {
                int load = 0;
                for (size_t i = 0; i < n; ++i)
                    if (vals[i] <= t && t < vals[i] + lengths[i])
                        load += heights[i];
                if (load > capacity)
                    return false;
            }
            return true;
        };

        vector<pair<int, int>> all_ranges = start_ranges;
        all_ranges.push_back(cap_range);

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, all_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> starts;
        for (auto & [lo, hi] : start_ranges)
            starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        auto cap = p.create_integer_variable(Integer{cap_range.first}, Integer{cap_range.second});

        vector<IntegerVariableID> lengths_v, heights_v;
        for (auto l : lengths)
            lengths_v.push_back(constant_variable(Integer{l}));
        for (auto h : heights)
            heights_v.push_back(constant_variable(Integer{h}));

        p.post(Cumulative{starts, lengths_v, heights_v, cap});

        vector<IntegerVariableID> all_vars = starts;
        all_vars.push_back(cap);

        auto proof_name = proofs ? make_optional("cumulative_test_varcap_" + tag) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{all_vars});
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Start-variable positions wrapped by the single-position sweep. The
    // fixed and random data top out at 4 tasks, so a single-position index
    // beyond this would wrap nothing on any test; detect and skip rather
    // than emit a duplicate bare run. mixed/uniform wrap every position.
    constexpr int n_positions = 4;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "cumulative view sweep: position {} out of range for n_positions = {}; skipping",
            *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    // Each test: { start_ranges, lengths, heights, capacity }
    // Kept small because stage-1 propagation is a pure checker: the solver
    // brute-forces through every assignment.
    vector<tuple<vector<pair<int, int>>, vector<int>, vector<int>, int>> data = {
        // Two tasks, unit demands, capacity 1: must not overlap.
        {{{0, 3}, {0, 3}}, {2, 2}, {1, 1}, 1},
        // Two tasks, unit demands, capacity 2: anything is fine.
        {{{0, 3}, {0, 3}}, {2, 2}, {1, 1}, 2},
        // Asymmetric heights with cap 2: tasks can overlap iff one has h=0
        // ... but here both are >0. Bigger task pushes any overlap over cap.
        {{{0, 3}, {0, 3}}, {2, 2}, {2, 1}, 2},
        // Tight three-task instance.
        {{{0, 2}, {0, 2}, {0, 2}}, {2, 1, 1}, {1, 1, 1}, 2},
        // Three tasks, capacity 1, all unit-height: nothing can overlap.
        {{{0, 3}, {0, 3}, {0, 3}}, {1, 1, 2}, {1, 1, 1}, 1},
        // Zero-length task should not constrain anything.
        {{{0, 2}, {0, 2}, {0, 2}}, {0, 2, 2}, {1, 1, 1}, 1},
        // Zero-height task should not constrain anything.
        {{{0, 2}, {0, 2}, {0, 2}}, {2, 2, 2}, {0, 1, 1}, 1},
        // Capacity 0 with all heights > 0: any active task violates.
        {{{0, 2}, {0, 2}}, {1, 1}, {1, 1}, 0},
        // Single task, vacuously satisfiable.
        {{{0, 4}}, {3}, {2}, 2},
        // Single task with capacity below height: unsatisfiable.
        {{{0, 4}}, {1}, {3}, 2},
        // Two tasks of differing lengths, cap 1: gaps matter.
        {{{0, 3}, {0, 3}}, {1, 2}, {1, 1}, 1},
    };

    // Random instances for breadth. Kept small because search is exhaustive
    // and the constraint is enumerated via brute-force over the start
    // domains: a wider horizon multiplies the enumeration cost across all
    // tasks. Sized so total runtime stays under a second even unoptimised.
    random_device rand_dev;
    mt19937 rand(rand_dev());

    auto random_instance = [&](int n, int max_start, int max_length, int max_height, int max_cap)
        -> tuple<vector<pair<int, int>>, vector<int>, vector<int>, int> {
        uniform_int_distribution<> lo_dist(0, max_start), span_dist(0, max_start),
            len_dist(0, max_length), ht_dist(0, max_height), cap_dist(0, max_cap);
        vector<pair<int, int>> sr;
        vector<int> lens, hts;
        for (int i = 0; i < n; ++i) {
            auto lo = lo_dist(rand), span = span_dist(rand);
            sr.emplace_back(lo, min(lo + span, max_start));
            lens.push_back(len_dist(rand));
            hts.push_back(ht_dist(rand));
        }
        return {sr, lens, hts, cap_dist(rand)};
    };

    // 25 small random cases (n=2 or 3, narrow horizons).
    for (int k = 0; k < 25; ++k) {
        uniform_int_distribution<> n_dist(2, 3);
        data.emplace_back(random_instance(n_dist(rand), 3, 3, 2, 3));
    }

    // 15 medium random cases (n=3 or 4, wider domains). TT should keep
    // these fast; verifies it actually does propagation.
    for (int k = 0; k < 15; ++k) {
        uniform_int_distribution<> n_dist(3, 4);
        data.emplace_back(random_instance(n_dist(rand), 4, 3, 2, 4));
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [sr, lens, hts, cap] : data)
            run_cumulative_test(proofs, view_cfg, sr, lens, hts, cap);

        // Dup tests use bare variables (the harness duplicates a handle into
        // several task positions); only run them when no wrapping is in
        // effect, to avoid duplicating the bare coverage under every wrap.
        if (run_dup) {
            // Two tasks sharing a start variable: their heights add at every
            // time point in their (intersecting) durations.
            // Capacity 2, two unit-height tasks: must fit (sum = 2). OK.
            run_dup_cumulative_test(proofs, {{0, 3}}, {0, 0}, {2, 2}, {1, 1}, 2);
            // Capacity 1, two unit-height tasks sharing a start: load=2 > cap=1
            // → UNSAT.
            run_dup_cumulative_test(proofs, {{0, 3}}, {0, 0}, {2, 2}, {1, 1}, 1);
            // Three tasks, two of which share a start. Third has its own start.
            run_dup_cumulative_test(proofs, {{0, 3}, {0, 3}}, {0, 0, 1},
                {2, 2, 1}, {1, 1, 1}, 2);

            // Variable-capacity instances. The capacity is a decision variable
            // enumerated alongside the starts.
            // Small: exercise cap = 0..2 directly.
            run_cumulative_var_cap_test(proofs, "small", {{0, 3}, {0, 3}}, {2, 2}, {1, 1}, {0, 2});
            // Three tasks, cap 1..3.
            run_cumulative_var_cap_test(proofs, "mid", {{0, 4}, {0, 4}, {0, 4}},
                {2, 2, 1}, {1, 1, 1}, {1, 3});
            // Wide values, tight capacity: heights 20/25 can't coexist under any
            // allowed capacity, so the structure is no-overlap; exercises the
            // capacity bit-encoding at realistic magnitudes (>4 bits).
            run_cumulative_var_cap_test(proofs, "wide_tight", {{0, 8}, {0, 8}},
                {3, 4}, {20, 25}, {25, 27});
            // Wide values, capacity range spans the overlap threshold (heights
            // 30+30=60): cap 55..62 forbids overlap at the low end and allows it
            // at the high end, exercising both the push and the contradiction.
            run_cumulative_var_cap_test(proofs, "wide_span", {{0, 6}, {0, 6}},
                {3, 3}, {30, 30}, {55, 62});
        }
    }

    return EXIT_SUCCESS;
}
