#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/mult_bc.hh>
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
using std::uniform_int_distribution;
using std::vector;

using fmt::print;
using fmt::println;

using namespace gcs;
using namespace gcs::test_innards;

auto run_mult_test(bool proofs, pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range, const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    print(cerr, "mult {} {} {} {}", v1_range, v2_range, v3_range, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
    p.post(MultBC{v1, v2, v3});

    auto proof_name = proofs ? make_optional("mult_bc_test") : nullopt;

    // TODO: Check for bounds(R)-consistency (currently the check is for bounds(Z))
    solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>>> data = {
        {{2, 5}, {1, 6}, {1, 12}},
        {{1, 6}, {2, 5}, {5, 8}},
        {{1, 3}, {1, 3}, {0, 10}},
        {{1, 3}, {1, 3}, {1, 3}},
        {{1, 5}, {6, 8}, {-10, 10}},
        {{1, 1}, {2, 4}, {-5, 5}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));

    for (auto & [r1, r2, r3] : data) {
        run_mult_test(false, r1, r2, r3, [](int a, int b, int c) { return a * b == c; });
    }

    if (can_run_veripb())
        for (auto & [r1, r2, r3] : data) {
            run_mult_test(true, r1, r2, r3, [](int a, int b, int c) { return a * b == c; });
        }

    return EXIT_SUCCESS;
}

// auto main(int, char *[]) -> int
//{
//     Problem p;
//     auto v1 = p.create_integer_variable(-6_i, 3_i);
//     auto v2 = p.create_integer_variable(-10_i, 3_i);
//     auto v3 = p.create_integer_variable(-1_i, 7_i);
//     p.post(MultBC{v1, v2, v3});
//     solve(
//         p, [&](const CurrentState &) -> bool { return true; }, make_optional(ProofOptions{"mult_bc.opb", "mult_bc.pbp"}));
//     system("veripb --trace --useColor mult_bc.opb mult_bc.pbp");
//     return EXIT_SUCCESS;
// }