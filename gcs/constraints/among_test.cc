#include <gcs/constraints/among.hh>
#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
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
#include <fmt/std.h>

using std::cerr;
using std::count;
using std::count_if;
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

auto run_among_test(bool proofs, variant<int, pair<int, int>> result_range, const vector<int> & voi, const vector<variant<int, pair<int, int>>> & array_range) -> void
{
    visit([&](auto result) { print(cerr, "among {} {} {} {}", result, voi, array_range, proofs ? " with proofs:" : ":"); }, result_range);
    cerr << flush;

    auto is_satisfying = [&](int n, const vector<int> & a) {
        return n == count_if(a.begin(), a.end(), [&](int v) { return 0 != count(voi.begin(), voi.end(), v); });
    };

    set<tuple<int, vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, result_range, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto result = visit([&](auto r) { return create_integer_variable_or_constant(p, r); }, result_range);
    vector<IntegerVariableID> array;
    for (const auto & a : array_range)
        array.push_back(visit([&](auto a) { return create_integer_variable_or_constant(p, a); }, a));
    vector<Integer> voi_i;
    for (const auto & v : voi)
        voi_i.push_back(Integer(v));
    p.post(Among{array, voi_i, result});

    auto proof_name = proofs ? make_optional("among_test") : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{result, CheckConsistency::GAC}, pair{array, CheckConsistency::GAC}});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<
        variant<int, pair<int, int>>,
        vector<int>,
        vector<variant<int, pair<int, int>>>>>
        data = {
            {pair{1, 3}, vector{2, 4, 6, 8}, {pair{1, 10}, pair{1, 10}, pair{1, 10}}},
            {pair{1, 5}, vector{1, 2, 3}, {pair{1, 5}, pair{1, 5}, pair{1, 5}}},
            {pair{1, 1}, vector{1, 2, 3}, {pair{1, 5}, pair{1, 5}, pair{1, 5}}},
            {pair{3, 5}, vector{1, 3}, {pair{1, 2}, pair{1, 2}, pair{1, 5}}},
            {pair{0, 5}, vector{1, 3}, {pair{1, 2}, pair{1, 2}, pair{1, 5}}},
            {pair{1, 5}, vector{2, 3, 2, 3, 3}, {pair{1, 5}, pair{1, 5}, pair{1, 5}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values_1 = n_values_dist(rand);
        auto n_values_2 = n_values_dist(rand);
        uniform_int_distribution values_dist(-10, 10);
        generate_random_data(rand, data,
            random_bounds(-7, 7, 5, 10),
            vector{size_t(n_values_1), values_dist},
            vector{size_t(n_values_2), random_bounds_or_constant(-5, 8, 3, 8)});
    }

    for (auto & [r1, r2, r3] : data)
        run_among_test(false, r1, r2, r3);

    if (can_run_veripb())
        for (auto & [r1, r2, r3] : data)
            run_among_test(true, r1, r2, r3);

    return EXIT_SUCCESS;
}
