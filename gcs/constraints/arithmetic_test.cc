#include <gcs/constraints/arithmetic.hh>
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
using std::uniform_int_distribution;
using std::vector;

using fmt::print;
using fmt::println;

using namespace gcs;
using namespace gcs::test_innards;

namespace
{
    template <typename Arithmetic_>
    struct NameOf;

    template <>
    struct NameOf<Plus>
    {
        static const constexpr auto name = "plus";
    };

    template <>
    struct NameOf<Minus>
    {
        static const constexpr auto name = "minus";
    };

    template <>
    struct NameOf<Times>
    {
        static const constexpr auto name = "times";
    };

    template <>
    struct NameOf<Div>
    {
        static const constexpr auto name = "div";
    };

    template <>
    struct NameOf<Mod>
    {
        static const constexpr auto name = "mod";
    };
}

template <typename Arithmetic_>
auto run_arithmetic_test(bool proofs, pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range, const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    print(cerr, "arithmetic {} {} {} {} {}", NameOf<Arithmetic_>::name, v1_range, v2_range, v3_range, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
    p.post(Arithmetic_{v1, v2, v3});

    auto proof_name = proofs ? make_optional("arithmetic_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});

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
        run_arithmetic_test<Plus>(false, r1, r2, r3, [](int a, int b, int c) { return a + b == c; });
        run_arithmetic_test<Minus>(false, r1, r2, r3, [](int a, int b, int c) { return a - b == c; });
        run_arithmetic_test<Times>(false, r1, r2, r3, [](int a, int b, int c) { return a * b == c; });
        run_arithmetic_test<Div>(false, r1, r2, r3, [](int a, int b, int c) { return 0 != b && a / b == c; });
        run_arithmetic_test<Mod>(false, r1, r2, r3, [](int a, int b, int c) { return 0 != b && a % b == c; });
    }

    if (can_run_veripb())
        for (auto & [r1, r2, r3] : data) {
            run_arithmetic_test<Plus>(true, r1, r2, r3, [](int a, int b, int c) { return a + b == c; });
            run_arithmetic_test<Minus>(true, r1, r2, r3, [](int a, int b, int c) { return a - b == c; });
            run_arithmetic_test<Times>(true, r1, r2, r3, [](int a, int b, int c) { return a * b == c; });
            run_arithmetic_test<Div>(true, r1, r2, r3, [](int a, int b, int c) { return 0 != b && a / b == c; });
            run_arithmetic_test<Mod>(true, r1, r2, r3, [](int a, int b, int c) { return 0 != b && a % b == c; });
        }

    return EXIT_SUCCESS;
}
