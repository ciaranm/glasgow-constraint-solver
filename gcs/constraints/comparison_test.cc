#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

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

using namespace std::literals::string_literals;

using namespace gcs;
using namespace gcs::test_innards;

namespace
{
    template <typename Comparison_>
    struct NameOf;

    template <>
    struct NameOf<LessThan>
    {
        static const constexpr auto name = "less than";
    };

    template <>
    struct NameOf<LessThanEqual>
    {
        static const constexpr auto name = "less than or equal";
    };

    template <>
    struct NameOf<GreaterThan>
    {
        static const constexpr auto name = "greater than";
    };

    template <>
    struct NameOf<GreaterThanEqual>
    {
        static const constexpr auto name = "greater than or equal";
    };

    template <>
    struct NameOf<LessThanIf>
    {
        static const constexpr auto name = "less than if";
    };

    template <>
    struct NameOf<LessThanIff>
    {
        static const constexpr auto name = "less than iff";
    };

    template <>
    struct NameOf<LessThanEqualIff>
    {
        static const constexpr auto name = "less than or equal iff";
    };

    template <>
    struct NameOf<GreaterThanIff>
    {
        static const constexpr auto name = "greater than iff";
    };

    template <>
    struct NameOf<GreaterThanEqualIff>
    {
        static const constexpr auto name = "greater than or equal iff";
    };
}

template <typename Constraint_>
auto run_binary_comparison_test(bool proofs, pair<int, int> v1_range, pair<int, int> v2_range, const function<auto(int, int)->bool> & is_satisfying) -> void
{
    print(cerr, "comparison {} {} {} {}", NameOf<Constraint_>::name, v1_range, v2_range, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<pair<int, int>> expected, actual;

    build_expected(expected, is_satisfying, v1_range, v2_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    p.post(Constraint_{v1, v2});

    auto proof_name = proofs ? make_optional("comparison_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2});

    check_results(proof_name, expected, actual);
}

template <typename Constraint_>
auto run_reif_binary_comparison_test(bool proofs, pair<int, int> v1_range, pair<int, int> v2_range, const function<auto(int, int)->bool> & is_satisfying, bool full) -> void
{
    print(cerr, "{} comparison {} {} {} {}", full ? "full reif" : "reif", NameOf<Constraint_>::name, v1_range, v2_range, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    build_expected(
        expected, [&](int a, int b, int r) -> bool {
            return full ? (r == is_satisfying(a, b)) : ((! r) || is_satisfying(a, b));
        },
        v1_range, v2_range, pair{0, 1});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    auto v3 = p.create_integer_variable(0_i, 1_i);
    p.post(Constraint_{v1, v2, v3 == 1_i});

    auto proof_name = proofs ? make_optional("comparison_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<pair<pair<int, int>, pair<int, int>>> data = {
        {{2, 5}, {1, 6}},
        {{1, 6}, {2, 5}},
        {{1, 3}, {1, 3}},
        {{1, 5}, {6, 8}},
        {{1, 1}, {2, 4}},
        {{1, 1}, {-3, 3}},
        {{1, 1}, {1, 3}},
        {{1, 1}, {2, 3}},
        {{1, 1}, {-3, 0}},
        {{1, 1}, {2, 2}},
        {{2, 2}, {1, 1}},
        {{1, 1}, {1, 1}},
        {{-2, -2}, {-2, -1}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));

    for (auto & [r1, r2] : data) {
        run_binary_comparison_test<LessThan>(false, r1, r2, [](int a, int b) { return a < b; });
        run_binary_comparison_test<LessThanEqual>(false, r1, r2, [](int a, int b) { return a <= b; });
        run_binary_comparison_test<GreaterThan>(false, r1, r2, [](int a, int b) { return a > b; });
        run_binary_comparison_test<GreaterThanEqual>(false, r1, r2, [](int a, int b) { return a >= b; });
        run_reif_binary_comparison_test<LessThanIf>(
            false, r1, r2, [](int a, int b) { return a < b; }, false);
        run_reif_binary_comparison_test<LessThanIff>(
            false, r1, r2, [](int a, int b) { return a < b; }, true);
        run_reif_binary_comparison_test<LessThanEqualIff>(
            false, r1, r2, [](int a, int b) { return a <= b; }, true);
        run_reif_binary_comparison_test<GreaterThanIff>(
            false, r1, r2, [](int a, int b) { return a > b; }, true);
        run_reif_binary_comparison_test<GreaterThanEqualIff>(
            false, r1, r2, [](int a, int b) { return a >= b; }, true);
    }

    if (can_run_veripb())
        for (auto & [r1, r2] : data) {
            run_binary_comparison_test<LessThan>(true, r1, r2, [](int a, int b) { return a < b; });
            run_binary_comparison_test<LessThanEqual>(true, r1, r2, [](int a, int b) { return a <= b; });
            run_binary_comparison_test<GreaterThan>(true, r1, r2, [](int a, int b) { return a > b; });
            run_binary_comparison_test<GreaterThanEqual>(true, r1, r2, [](int a, int b) { return a >= b; });
            run_reif_binary_comparison_test<LessThanIf>(
                true, r1, r2, [](int a, int b) { return a < b; }, false);
            run_reif_binary_comparison_test<LessThanIff>(
                true, r1, r2, [](int a, int b) { return a < b; }, true);
            run_reif_binary_comparison_test<LessThanEqualIff>(
                true, r1, r2, [](int a, int b) { return a <= b; }, true);
            run_reif_binary_comparison_test<GreaterThanIff>(
                true, r1, r2, [](int a, int b) { return a > b; }, true);
            run_reif_binary_comparison_test<GreaterThanEqualIff>(
                true, r1, r2, [](int a, int b) { return a >= b; }, true);
        }

    return EXIT_SUCCESS;
}
