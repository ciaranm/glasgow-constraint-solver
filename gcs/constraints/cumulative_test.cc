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
    auto run_cumulative_test(bool proofs, const vector<pair<int, int>> & start_ranges,
        const vector<int> & lengths, const vector<int> & heights, int capacity) -> void
    {
        print(cerr, "cumulative {} {} {} c={}{}", start_ranges, lengths, heights, capacity,
            proofs ? " with proofs:" : ":");
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
        for (auto & [lo, hi] : start_ranges)
            starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));

        vector<Integer> lengths_i, heights_i;
        for (auto l : lengths)
            lengths_i.push_back(Integer{l});
        for (auto h : heights)
            heights_i.push_back(Integer{h});

        p.post(Cumulative{starts, lengths_i, heights_i, Integer{capacity}});

        auto proof_name = proofs ? make_optional("cumulative_test") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{starts});

        check_results(proof_name, expected, actual);
    }
}

auto main(int, char *[]) -> int
{
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
            run_cumulative_test(proofs, sr, lens, hts, cap);
    }

    return EXIT_SUCCESS;
}
