#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/count.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>

using std::cerr;
using std::flush;
using std::function;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::to_string;
using std::tuple;
using std::uniform_int_distribution;
using std::variant;
using std::vector;

using fmt::print;
using fmt::println;

using namespace gcs;
using namespace gcs::test_innards;

auto run_count_test(bool proofs, variant<int, pair<int, int>> result_range, variant<int, pair<int, int>> voi_range, const vector<pair<int, int>> & array_range) -> void
{
    visit([&](auto result, auto voi) { print(cerr, "count {} {} {} {}", result, voi, array_range, proofs ? " with proofs:" : ":"); }, result_range, voi_range);
    cerr << flush;

    auto is_satisfying = [](int v, int n, const vector<int> & a) {
        return n == count(a.begin(), a.end(), v);
    };

    set<tuple<int, int, vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, voi_range, result_range, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto result = visit([&](auto r) { return create_integer_variable_or_constant(p, r); }, result_range);
    auto voi = visit([&](auto v) { return create_integer_variable_or_constant(p, v); }, voi_range);
    vector<IntegerVariableID> array;
    for (const auto & [l, u] : array_range)
        array.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    p.post(Count{array, voi, result});

    auto proof_name = proofs ? make_optional("count_test") : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{voi, CheckConsistency::GAC}, pair{result, CheckConsistency::GAC}, pair{array, CheckConsistency::None}});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<variant<int, pair<int, int>>, variant<int, pair<int, int>>, vector<pair<int, int>>>> data = {
        {pair{1, 2}, pair{1, 2}, {{1, 2}, {1, 2}}},
        {pair{1, 2}, pair{0, 3}, {{1, 2}, {1, 2}}},
        {pair{1, 2}, pair{1, 2}, {{1, 2}, {1, 2}, {1, 2}}},
        {pair{0, 3}, pair{1, 2}, {{1, 2}, {1, 2}, {1, 2}}},
        {pair{0, 4}, pair{0, 4}, {{1, 2}, {1, 2}, {1, 2}}},
        {pair{1, 3}, pair{1, 6}, {{0, 4}, {0, 5}, {0, 6}}},
        {pair{-1, 3}, pair{0, 5}, {{-1, 2}, {1, 3}, {4, 5}}},
        {pair{1, 4}, pair{-3, 8}, {{1, 4}, {2, 3}, {0, 5}, {-2, 0}, {5, 7}}},
        {pair{0, 4}, pair{-5, 2}, {{7, 14}, {7, 11}}},
        {pair{3, 10}, pair{3, 8}, {{-2, 2}, {3, 7}, {5, 9}, {0, 6}}},
        {pair{1, 9}, pair{-5, 5}, {{2, 6}, {8, 11}, {6, 12}, {-3, 0}}},
        {pair{2, 2}, pair{3, 6}, {{5, 9}, {-5, 3}, {2, 6}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_bounds(-7, 7, 5, 10), random_bounds(-7, 7, 5, 10),
            vector{size_t(n_values), random_bounds(-5, 8, 3, 8)});
    }

    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_constant(-7, 7), random_bounds(-7, 7, 5, 10),
            vector{size_t(n_values), random_bounds(-5, 8, 3, 8)});
    }

    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_constant(-7, 7), random_constant(-7, 7),
            vector{size_t(n_values), random_bounds(-5, 8, 3, 8)});
    }

    for (auto & [r1, r2, r3] : data)
        run_count_test(false, r1, r2, r3);

    if (can_run_veripb())
        for (auto & [r1, r2, r3] : data)
            run_count_test(true, r1, r2, r3);

    return EXIT_SUCCESS;
}
