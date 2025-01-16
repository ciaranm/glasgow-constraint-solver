#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/not_equals.hh>
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
using std::vector;

using fmt::print;
using fmt::println;

using namespace gcs;
using namespace gcs::test_innards;

auto run_all_different_test(bool proofs, pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range,
    pair<int, int> v4_range, pair<int, int> v5_range, pair<int, int> v6_range) -> void
{
    print(cerr, "all_different {} {} {} {} {} {} {}", v1_range, v2_range, v3_range, v4_range, v5_range, v6_range,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [](int a, int b, int c, int d, int e, int f) {
        return a != b && a != c && a != d && a != e && a != f && b != c && b != d && b != e && b != f && c != d && c != e && c != f && d != e && d != f && e != f;
    };

    set<tuple<int, int, int, int, int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range, v4_range, v5_range, v6_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
    auto v4 = p.create_integer_variable(Integer(v4_range.first), Integer(v4_range.second));
    auto v5 = p.create_integer_variable(Integer(v5_range.first), Integer(v5_range.second));
    auto v6 = p.create_integer_variable(Integer(v6_range.first), Integer(v6_range.second));
    p.post(AllDifferent{vector<IntegerVariableID>{v1, v2, v3, v4, v5, v6}, true});

    auto proof_name = proofs ? make_optional("all_different_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, v4, v5, v6});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>, pair<int, int>, pair<int, int>, pair<int, int>>> data = {
        {{1, 6}, {1, 6}, {1, 6}, {1, 6}, {1, 6}, {1, 6}},
        {{0, 5}, {1, 6}, {2, 7}, {3, 8}, {4, 9}, {5, 6}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 2, 5), random_bounds(-10, 10, 2, 5), random_bounds(-10, 10, 2, 5),
            random_bounds(-10, 10, 2, 5), random_bounds(-10, 10, 2, 5), random_bounds(-10, 10, 2, 5));

    for (auto & [r1, r2, r3, r4, r5, r6] : data)
        run_all_different_test(false, r1, r2, r3, r4, r5, r6);

    if (can_run_veripb())
        for (auto & [r1, r2, r3, r4, r5, r6] : data)
            run_all_different_test(true, r1, r2, r3, r4, r5, r6);

    return EXIT_SUCCESS;
}
