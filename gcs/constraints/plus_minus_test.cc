#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/minus.hh>
#include <gcs/constraints/plus.hh>
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
using std::variant;
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
}

template <typename Constraint_, typename V1_, typename V2_, typename V3_>
auto run_plus_minus_test(bool proofs, V1_ v1_range, V2_ v2_range, V3_ v3_range, const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    visit([&](const auto & v1, const auto & v2) {
        print(cerr, "{} {} {} {} {}", NameOf<Constraint_>::name, v1, v2, v3_range, proofs ? " with proofs:" : ":");
    },
        v1_range, v2_range);
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    visit([&](const auto & v1, const auto & v2) {
        build_expected(expected, is_satisfying, v1, v2, v3_range);
    },
        v1_range, v2_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](const auto & r) { return create_integer_variable_or_constant(p, r); }, v1_range);
    auto v2 = visit([&](const auto & r) { return create_integer_variable_or_constant(p, r); }, v2_range);
    auto v3 = create_integer_variable_or_constant(p, v3_range);
    p.post(Constraint_{v1, v2, v3});

    auto proof_name = proofs ? make_optional("plus_minus_test") : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{v1, CheckConsistency::None}, pair{v2, CheckConsistency::None}, pair{v3, CheckConsistency::None}});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<variant<pair<int, int>, vector<int>>, variant<pair<int, int>, vector<int>>, pair<int, int>>> data = {
        {pair{2, 5}, pair{1, 6}, {1, 12}},
        {pair{1, 6}, pair{2, 5}, {5, 8}},
        {pair{1, 3}, pair{1, 3}, {0, 10}},
        {pair{1, 3}, pair{1, 3}, {1, 3}},
        {pair{1, 5}, pair{6, 8}, {-10, 10}},
        {pair{1, 1}, pair{2, 4}, {-5, 5}},
        {pair{10, 15}, pair{60, 80}, {-100, 100}},
        {pair{-10, 0}, pair{-4, 2}, {4, 9}},
        {pair{1, 100}, pair{1, 3}, {1, 100}},
        {pair{1, 10}, pair{1, 3}, {1, 10}},
        {pair{1, 10}, pair{1, 10}, {1, 20}},
        {vector{1, 5, 10}, vector{1, 5, 10}, {1, 20}},
        {vector{1, 2, 3, 5, 6, 10}, vector{1, 2, 3, 5, 8, 9, 10}, {1, 20}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));

    for (auto & [r1, r2, r3] : data) {
        run_plus_minus_test<Plus>(false, r1, r2, r3, [](int a, int b, int c) { return a + b == c; });
        run_plus_minus_test<Minus>(false, r1, r2, r3, [](int a, int b, int c) { return a - b == c; });
    }

    if (can_run_veripb())
        for (auto & [r1, r2, r3] : data) {
            run_plus_minus_test<Plus>(true, r1, r2, r3, [](int a, int b, int c) { return a + b == c; });
            run_plus_minus_test<Minus>(true, r1, r2, r3, [](int a, int b, int c) { return a - b == c; });
        }

    return EXIT_SUCCESS;
}
