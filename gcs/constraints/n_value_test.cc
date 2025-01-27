#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/n_value.hh>
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

using std::cerr;
using std::cmp_equal;
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

auto run_n_value_test(bool proofs, variant<int, pair<int, int>> result_range, const vector<pair<int, int>> & array_range) -> void
{
    visit([&](auto r) { print(cerr, "nvalue {} {} {}", r, array_range, proofs ? " with proofs:" : ":"); }, result_range);
    cerr << flush;

    set<tuple<int, vector<int>>> expected, actual;
    auto is_satisfying = [&](int n, const vector<int> & v) -> bool {
        set<int> s{v.begin(), v.end()};
        return cmp_equal(n, s.size());
    };
    build_expected(expected, is_satisfying, result_range, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto result = visit([&](auto r) { return create_integer_variable_or_constant(p, r); }, result_range);
    vector<IntegerVariableID> array;
    for (const auto & [l, u] : array_range)
        array.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    p.post(NValue{result, array});

    auto proof_name = proofs ? make_optional("n_value_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{result, array});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<variant<int, pair<int, int>>, vector<pair<int, int>>>> data = {
        {pair{1, 2}, {{1, 2}, {1, 2}}},
        {pair{1, 2}, {{1, 2}, {1, 2}, {1, 2}}},
        {pair{0, 4}, {{1, 2}, {1, 2}, {1, 2}}},
        {pair{1, 3}, {{0, 4}, {0, 5}, {0, 6}}},
        {pair{-1, 3}, {{-1, 2}, {1, 3}, {4, 5}}},
        {pair{1, 4}, {{1, 4}, {2, 3}, {0, 5}, {-2, 0}, {5, 7}}},
        {pair{-5, 5}, {{-8, 0}, {4, 4}, {10, 10}, {2, 11}, {4, 10}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 5);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_bounds(-5, 5, 2, 7), vector(n_values, random_bounds(-5, 5, 2, 7)));
    }

    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 5);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_constant(-5, 5), vector(n_values, random_bounds(-5, 5, 2, 7)));
    }

    for (auto & [r1, r2] : data)
        run_n_value_test(false, r1, r2);

    if (can_run_veripb())
        for (auto & [r1, r2] : data)
            run_n_value_test(true, r1, r2);

    return EXIT_SUCCESS;
}
