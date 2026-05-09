#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/parity.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <set>
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
using std::count_if;
using std::flush;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::tuple;
using std::uniform_int_distribution;
using std::variant;
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

auto run_parity_test(bool proofs, const vector<variant<int, pair<int, int>>> & array_range) -> void
{
    print(cerr, "parity odd {} {}", array_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [](const vector<int> & a) {
        return count_if(a.begin(), a.end(), [](int x) { return x != 0; }) % 2 == 1;
    };

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> array;
    for (const auto & entry : array_range)
        array.push_back(visit([&](const auto & e) { return create_integer_variable_or_constant(p, e); }, entry));
    p.post(ParityOdd{array});

    auto proof_name = proofs ? make_optional("parity_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{array});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    using Entry = variant<int, pair<int, int>>;
    vector<vector<Entry>> data = {
        // Boundary: empty array — UNSAT (0 is even, not odd).
        {},
        // Singleton over {0, 1} — only x=1 satisfies.
        {pair{0, 1}},
        // Existing tight {0,1} cases.
        {pair{0, 1}, pair{0, 1}},
        {pair{0, 1}, pair{0, 1}, pair{0, 1}},
        {pair{0, 1}, pair{0, 1}, pair{0, 1}, pair{0, 1}},
        // Wider non-binary domains — predicate is "nonzero count is odd",
        // so any nonzero value contributes.
        {pair{0, 4}, pair{0, 4}, pair{0, 4}},
        {pair{-3, 3}, pair{-3, 3}},
        // Domains that don't include 0 — every entry is nonzero.
        {pair{1, 5}, pair{1, 5}, pair{1, 5}},
        {pair{-3, -1}, pair{1, 3}},
        // Constant entries: a fixed nonzero contributes 1 to the count;
        // a fixed 0 contributes nothing.
        {1, pair{0, 3}, pair{0, 3}},
        {0, pair{0, 3}, pair{0, 3}},
        {3, 0, pair{0, 3}, pair{0, 3}},
        // All-constant infeasible (count = 2, even).
        {1, 1, 0},
        // All-constant feasible (count = 1, odd).
        {1, 0, 0}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values = n_values_dist(rand);
        // random_bounds_or_constant occasionally produces a constant entry,
        // mixing with bounds-pairs over {-1..2}..{1..4}. Predicate handles
        // any int value — only zero/non-zero matters — so wide ranges are safe.
        generate_random_data(rand, data, vector{size_t(n_values), random_bounds_or_constant(-1, 2, 1, 4)});
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & v : data)
            run_parity_test(proofs, v);
    }

    return EXIT_SUCCESS;
}
