#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
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
using std::tuple;
using std::variant;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

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
    struct NameOf<GreaterThanIf>
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
    struct NameOf<LessThanEqualIf>
    {
        static const constexpr auto name = "less than or equal if";
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
    struct NameOf<GreaterThanEqualIf>
    {
        static const constexpr auto name = "greater than or equal if";
    };

    template <>
    struct NameOf<GreaterThanEqualIff>
    {
        static const constexpr auto name = "greater than or equal iff";
    };
}

template <typename Constraint_>
auto run_binary_comparison_test(bool proofs, const string & mode, variant<int, pair<int, int>> v1_range, variant<int, pair<int, int>> v2_range, const function<auto(int, int)->bool> & is_satisfying) -> void
{
    visit([&](auto v1, auto v2) { print(cerr, "comparison {} {} {} {}", NameOf<Constraint_>::name, v1, v2, proofs ? " with proofs:" : ":"); }, v1_range, v2_range);
    cerr << flush;
    set<pair<int, int>> expected, actual;

    build_expected(expected, is_satisfying, v1_range, v2_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v1_range);
    auto v2 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v2_range);
    p.post(Constraint_{v1, v2});

    auto proof_name = proofs ? make_optional("comparison_test_" + mode) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2});

    check_results(proof_name, expected, actual);
}

template <typename Constraint_>
auto run_reif_binary_comparison_test(bool proofs, const string & mode, variant<int, pair<int, int>> v1_range, variant<int, pair<int, int>> v2_range, const function<auto(int, int)->bool> & is_satisfying, bool full) -> void
{
    for (const auto & v3_range : vector<pair<int, int>>{{0, 0}, {1, 1}, {0, 1}}) {
        visit([&](auto v1, auto v2) { print(cerr, "{} comparison {} {} {} {} {}", full ? "full reif" : "reif",
                                          NameOf<Constraint_>::name, v1, v2, v3_range, proofs ? " with proofs:" : ":"); }, v1_range, v2_range);
        cerr << flush;
        set<tuple<int, int, int>> expected, actual;

        build_expected(
            expected, [&](int a, int b, int r) -> bool {
                return full ? (r == is_satisfying(a, b)) : ((! r) || is_satisfying(a, b));
            },
            v1_range, v2_range, v3_range);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto v1 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v1_range);
        auto v2 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v2_range);
        auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second), "c");
        p.post(Constraint_{v1, v2, v3 == 1_i});

        auto proof_name = proofs ? make_optional("comparison_test_" + mode) : nullopt;
        solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});

        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    if (argc != 2)
        throw UnimplementedException{};

    vector<pair<variant<int, pair<int, int>>, variant<int, pair<int, int>>>> data = {
        {pair{2, 5}, pair{1, 6}},
        {pair{1, 6}, pair{2, 5}},
        {pair{1, 3}, pair{1, 3}},
        {pair{1, 5}, pair{6, 8}},
        {pair{1, 1}, pair{2, 4}},
        {pair{1, 1}, pair{-3, 3}},
        {pair{1, 1}, pair{1, 3}},
        {pair{1, 1}, pair{2, 3}},
        {pair{1, 1}, pair{-3, 0}},
        {pair{1, 1}, pair{2, 2}},
        {pair{2, 2}, pair{1, 1}},
        {pair{1, 1}, pair{1, 1}},
        {pair{-2, -2}, pair{-2, -1}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_constant(-10, 10), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_constant(-10, 10));

    string mode{argv[1]};

    for (auto & [r1, r2] : data) {
        if (mode == "lt") {
            run_binary_comparison_test<LessThan>(false, mode, r1, r2, [](int a, int b) { return a < b; });
        }
        else if (mode == "lt_if") {
            run_reif_binary_comparison_test<LessThanIf>(false, mode, r1, r2, [](int a, int b) { return a < b; }, false);
        }
        else if (mode == "lt_iff") {
            run_reif_binary_comparison_test<LessThanIff>(false, mode, r1, r2, [](int a, int b) { return a < b; }, true);
        }
        else if (mode == "le") {
            run_binary_comparison_test<LessThanEqual>(false, mode, r1, r2, [](int a, int b) { return a <= b; });
        }
        else if (mode == "le_if") {
            run_reif_binary_comparison_test<LessThanEqualIf>(false, mode, r1, r2, [](int a, int b) { return a <= b; }, false);
        }
        else if (mode == "le_iff") {
            run_reif_binary_comparison_test<LessThanEqualIff>(false, mode, r1, r2, [](int a, int b) { return a <= b; }, true);
        }
        else if (mode == "gt") {
            run_binary_comparison_test<GreaterThan>(false, mode, r1, r2, [](int a, int b) { return a > b; });
        }
        else if (mode == "gt_if") {
            run_reif_binary_comparison_test<GreaterThanIf>(false, mode, r1, r2, [](int a, int b) { return a > b; }, false);
        }
        else if (mode == "gt_iff") {
            run_reif_binary_comparison_test<GreaterThanIff>(false, mode, r1, r2, [](int a, int b) { return a > b; }, true);
        }
        else if (mode == "ge") {
            run_binary_comparison_test<GreaterThanEqual>(false, mode, r1, r2, [](int a, int b) { return a >= b; });
        }
        else if (mode == "ge_if") {
            run_reif_binary_comparison_test<GreaterThanEqualIf>(false, mode, r1, r2, [](int a, int b) { return a >= b; }, false);
        }
        else if (mode == "ge_iff") {
            run_reif_binary_comparison_test<GreaterThanEqualIff>(false, mode, r1, r2, [](int a, int b) { return a >= b; }, true);
        }
        else
            throw UnimplementedException{};
    }

    if (can_run_veripb())
        for (auto & [r1, r2] : data) {
            if (mode == "lt") {
                run_binary_comparison_test<LessThan>(true, mode, r1, r2, [](int a, int b) { return a < b; });
            }
            else if (mode == "lt_if") {
                run_reif_binary_comparison_test<LessThanIf>(true, mode, r1, r2, [](int a, int b) { return a < b; }, false);
            }
            else if (mode == "lt_iff") {
                run_reif_binary_comparison_test<LessThanIff>(true, mode, r1, r2, [](int a, int b) { return a < b; }, true);
            }
            else if (mode == "le") {
                run_binary_comparison_test<LessThanEqual>(true, mode, r1, r2, [](int a, int b) { return a <= b; });
            }
            else if (mode == "le_if") {
                run_reif_binary_comparison_test<LessThanEqualIf>(true, mode, r1, r2, [](int a, int b) { return a <= b; }, false);
            }
            else if (mode == "le_iff") {
                run_reif_binary_comparison_test<LessThanEqualIff>(true, mode, r1, r2, [](int a, int b) { return a <= b; }, true);
            }
            else if (mode == "gt") {
                run_binary_comparison_test<GreaterThan>(true, mode, r1, r2, [](int a, int b) { return a > b; });
            }
            else if (mode == "gt_if") {
                run_reif_binary_comparison_test<GreaterThanIf>(true, mode, r1, r2, [](int a, int b) { return a > b; }, false);
            }
            else if (mode == "gt_iff") {
                run_reif_binary_comparison_test<GreaterThanIff>(true, mode, r1, r2, [](int a, int b) { return a > b; }, true);
            }
            else if (mode == "ge") {
                run_binary_comparison_test<GreaterThanEqual>(true, mode, r1, r2, [](int a, int b) { return a >= b; });
            }
            else if (mode == "ge_if") {
                run_reif_binary_comparison_test<GreaterThanEqualIf>(true, mode, r1, r2, [](int a, int b) { return a >= b; }, false);
            }
            else if (mode == "ge_iff") {
                run_reif_binary_comparison_test<GreaterThanEqualIff>(true, mode, r1, r2, [](int a, int b) { return a >= b; }, true);
            }
            else
                throw UnimplementedException{};
        }

    return EXIT_SUCCESS;
}
