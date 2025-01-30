#include <gcs/constraints/abs.hh>
#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
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
using std::variant;
using std::vector;

using fmt::print;
using fmt::println;

using namespace gcs;
using namespace gcs::test_innards;

auto run_abs_test(bool proofs, variant<int, pair<int, int>> v1_range, variant<int, pair<int, int>> v2_range) -> void
{
    visit([&](auto v1, auto v2) { print(cerr, "abs {} {} {}", v1, v2, proofs ? " with proofs:" : ":"); }, v1_range, v2_range);
    cerr << flush;

    auto is_satisfying = [](int a, int b) { return b == abs(a); };

    set<pair<int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v1_range);
    auto v2 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v2_range);
    p.post(Abs{v1, v2});

    auto proof_name = proofs ? make_optional("abs_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<pair<variant<int, pair<int, int>>, variant<int, pair<int, int>>>> data = {
        {pair{2, 5}, pair{1, 6}},
        {pair{1, 6}, pair{2, 5}},
        {pair{1, 3}, pair{1, 3}},
        {pair{1, 5}, pair{6, 8}},
        {pair{1, 1}, pair{2, 4}},
        {pair{-5, 5}, pair{-5, 5}},
        {pair{-1, 6}, pair{-2, 5}},
        {pair{1, 3}, pair{-1, 3}},
        {pair{-1, 5}, pair{-6, 8}},
        {pair{-1, 1}, pair{-2, 4}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_constant(-10, 10), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_constant(-10, 10));

    for (auto & [r1, r2] : data)
        run_abs_test(false, r1, r2);

    if (can_run_veripb())
        for (auto & [r1, r2] : data)
            run_abs_test(true, r1, r2);

    return EXIT_SUCCESS;
}
