#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

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
using std::min;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::string;
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
    auto run_disjunctive_test(bool proofs, const string & mode, bool strict,
        const vector<pair<int, int>> & start_ranges, const vector<int> & lengths) -> void
    {
        print(cerr, "disjunctive{} {} {}{}", strict ? "_strict" : "",
            start_ranges, lengths, proofs ? " with proofs:" : ":");
        cerr << flush;

        auto n = start_ranges.size();

        auto is_satisfying = [&](const vector<int> & starts) {
            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    // Non-strict: pairs involving a zero-length task float freely.
                    if (! strict && (lengths[i] == 0 || lengths[j] == 0))
                        continue;
                    bool i_before_j = starts[i] + lengths[i] <= starts[j];
                    bool j_before_i = starts[j] + lengths[j] <= starts[i];
                    if (! i_before_j && ! j_before_i)
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

        vector<Integer> lengths_i;
        for (auto l : lengths)
            lengths_i.push_back(Integer{l});

        p.post(Disjunctive{starts, lengths_i, strict});

        auto proof_name = proofs ? make_optional("disjunctive_test_" + mode) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{starts});

        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    if (argc != 2)
        throw UnimplementedException{};

    string mode{argv[1]};
    bool strict;
    if (mode == "strict")
        strict = true;
    else if (mode == "nonstrict")
        strict = false;
    else
        throw UnimplementedException{};

    // Each test: { start_ranges, lengths }
    // Kept small because stage-1 propagation is a pure checker: the solver
    // brute-forces through every assignment.
    vector<pair<vector<pair<int, int>>, vector<int>>> data = {
        // Two tasks must not overlap.
        {{{0, 3}, {0, 3}}, {2, 2}},
        // Asymmetric lengths.
        {{{0, 3}, {0, 3}}, {1, 2}},
        // Three tasks, tight horizon, must serialise to fit.
        {{{0, 2}, {0, 2}, {0, 2}}, {1, 1, 1}},
        // Three tasks of varying lengths.
        {{{0, 3}, {0, 3}, {0, 3}}, {1, 1, 2}},
        // Single task — vacuously satisfiable, filtered to < 2 active.
        {{{0, 4}}, {3}},
        // Trivially unsatisfiable: two length-2 tasks pinned to time 0.
        {{{0, 0}, {0, 0}}, {2, 2}},
        // One zero-length task alongside a non-zero one.
        {{{0, 2}, {0, 2}}, {0, 2}},
        // Two zero-length tasks.
        {{{0, 2}, {0, 2}}, {0, 0}},
    };

    // Random instances for breadth.
    random_device rand_dev;
    mt19937 rand(rand_dev());

    auto random_instance = [&](int n, int max_start, int max_length)
        -> pair<vector<pair<int, int>>, vector<int>> {
        uniform_int_distribution<> lo_dist(0, max_start), span_dist(0, max_start),
            len_dist(0, max_length);
        vector<pair<int, int>> sr;
        vector<int> lens;
        for (int i = 0; i < n; ++i) {
            auto lo = lo_dist(rand), span = span_dist(rand);
            sr.emplace_back(lo, min(lo + span, max_start));
            lens.push_back(len_dist(rand));
        }
        return {sr, lens};
    };

    // 25 small random cases (n=2 or 3, narrow horizons).
    for (int k = 0; k < 25; ++k) {
        uniform_int_distribution<> n_dist(2, 3);
        data.emplace_back(random_instance(n_dist(rand), 3, 3));
    }

    // 15 medium random cases (n=3 or 4, wider domains).
    for (int k = 0; k < 15; ++k) {
        uniform_int_distribution<> n_dist(3, 4);
        data.emplace_back(random_instance(n_dist(rand), 4, 3));
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [sr, lens] : data)
            run_disjunctive_test(proofs, mode, strict, sr, lens);
    }

    return EXIT_SUCCESS;
}
