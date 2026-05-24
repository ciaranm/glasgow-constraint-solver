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
auto run_binary_comparison_test(bool proofs, const string & mode, const ViewWrapConfig & view_cfg,
    variant<int, pair<int, int>> v1_range, variant<int, pair<int, int>> v2_range, const function<auto(int, int)->bool> & is_satisfying) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2);
    visit([&](auto v1, auto v2) { print(cerr, "comparison [{}] {} {} {} {}", view_wrap_config_label(view_cfg), NameOf<Constraint_>::name, v1, v2, proofs ? " with proofs:" : ":"); }, v1_range, v2_range);
    cerr << flush;
    set<pair<int, int>> expected, actual;

    build_expected(expected, is_satisfying, v1_range, v2_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(0)); }, v1_range);
    auto v2 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(1)); }, v2_range);
    p.post(Constraint_{v1, v2});

    auto proof_name = proofs ? make_optional("comparison_test_" + mode + "_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2});

    check_results(proof_name, expected, actual);
}

template <typename Constraint_>
auto run_reif_binary_comparison_test(bool proofs, const string & mode, const ViewWrapConfig & view_cfg,
    variant<int, pair<int, int>> v1_range, variant<int, pair<int, int>> v2_range, const function<auto(int, int)->bool> & is_satisfying, bool full) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2);
    for (const auto & v3_range : vector<pair<int, int>>{{0, 0}, {1, 1}, {0, 1}}) {
        visit([&](auto v1, auto v2) { print(cerr, "{} comparison [{}] {} {} {} {} {}", full ? "full reif" : "reif",
                                          view_wrap_config_label(view_cfg), NameOf<Constraint_>::name, v1, v2, v3_range, proofs ? " with proofs:" : ":"); }, v1_range, v2_range);
        cerr << flush;
        set<tuple<int, int, int>> expected, actual;

        build_expected(
            expected, [&](int a, int b, int r) -> bool {
                return full ? (r == is_satisfying(a, b)) : ((! r) || is_satisfying(a, b));
            },
            v1_range, v2_range, v3_range);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto v1 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(0)); }, v1_range);
        auto v2 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(1)); }, v2_range);
        auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second), "c");
        p.post(Constraint_{v1, v2, v3 == 1_i});

        auto proof_name = proofs ? make_optional("comparison_test_" + mode + "_" + view_wrap_config_label(view_cfg)) : nullopt;
        solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});

        check_results(proof_name, expected, actual);
    }
}

// Dup-variable test: post a binary comparison with the same handle in
// both slots. Consistency isn't checked on dup runs; see
// tmp/duplicate_var_audit.md.
template <typename Constraint_>
auto run_dup_binary_comparison_test(bool proofs, const string & mode, pair<int, int> x_range,
    const function<auto(int) -> bool> & is_satisfying) -> void
{
    print(cerr, "comparison dup {} {} {}", NameOf<Constraint_>::name, x_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int>> expected, actual;
    build_expected(expected, is_satisfying, x_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second));
    p.post(Constraint_{x, x});

    auto proof_name = proofs ? make_optional("comparison_test_" + mode + "_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x});

    check_results(proof_name, expected, actual);
}

template <typename Constraint_>
auto run_dup_reif_binary_comparison_test(bool proofs, const string & mode, pair<int, int> x_range,
    const function<auto(int, int) -> bool> & is_satisfying) -> void
{
    print(cerr, "comparison dup reif {} {} {}", NameOf<Constraint_>::name, x_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int>> expected, actual;
    build_expected(expected, is_satisfying, x_range, pair{0, 1});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second));
    auto c = p.create_integer_variable(0_i, 1_i, "c");
    p.post(Constraint_{x, x, c == 1_i});

    auto proof_name = proofs ? make_optional("comparison_test_" + mode + "_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x, c});

    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    // Mode is the first non-flag positional; --view-* flags may follow.
    string mode;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (! a.starts_with("--")) {
            mode = a;
            break;
        }
    }
    if (mode.empty())
        throw UnimplementedException{};

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 2;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "comparison view sweep: position {} out of range for n_positions = {}; skipping",
            *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

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

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2] : data) {
            if (mode == "lt") {
                run_binary_comparison_test<LessThan>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a < b; });
            }
            else if (mode == "lt_if") {
                run_reif_binary_comparison_test<LessThanIf>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a < b; }, false);
            }
            else if (mode == "lt_iff") {
                run_reif_binary_comparison_test<LessThanIff>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a < b; }, true);
            }
            else if (mode == "le") {
                run_binary_comparison_test<LessThanEqual>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a <= b; });
            }
            else if (mode == "le_if") {
                run_reif_binary_comparison_test<LessThanEqualIf>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a <= b; }, false);
            }
            else if (mode == "le_iff") {
                run_reif_binary_comparison_test<LessThanEqualIff>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a <= b; }, true);
            }
            else if (mode == "gt") {
                run_binary_comparison_test<GreaterThan>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a > b; });
            }
            else if (mode == "gt_if") {
                run_reif_binary_comparison_test<GreaterThanIf>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a > b; }, false);
            }
            else if (mode == "gt_iff") {
                run_reif_binary_comparison_test<GreaterThanIff>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a > b; }, true);
            }
            else if (mode == "ge") {
                run_binary_comparison_test<GreaterThanEqual>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a >= b; });
            }
            else if (mode == "ge_if") {
                run_reif_binary_comparison_test<GreaterThanEqualIf>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a >= b; }, false);
            }
            else if (mode == "ge_iff") {
                run_reif_binary_comparison_test<GreaterThanEqualIff>(proofs, mode, view_cfg, r1, r2, [](int a, int b) { return a >= b; }, true);
            }
            else
                throw UnimplementedException{};
        }

        // Dup-variable cases. Only the audit's OK variants are exercised here;
        // lt, gt, lt_if, gt_if are skipped (Bucket A throw / Bucket B fix).
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions)) {
            vector<pair<int, int>> dup_data = {{0, 0}, {0, 5}, {-3, 3}, {2, 5}};
            for (auto & xr : dup_data) {
                if (mode == "le")
                    run_dup_binary_comparison_test<LessThanEqual>(proofs, mode, xr,
                        [](int) { return true; });
                else if (mode == "ge")
                    run_dup_binary_comparison_test<GreaterThanEqual>(proofs, mode, xr,
                        [](int) { return true; });
                else if (mode == "le_if")
                    run_dup_reif_binary_comparison_test<LessThanEqualIf>(proofs, mode, xr,
                        [](int, int) { return true; });
                else if (mode == "ge_if")
                    run_dup_reif_binary_comparison_test<GreaterThanEqualIf>(proofs, mode, xr,
                        [](int, int) { return true; });
                else if (mode == "lt_iff")
                    run_dup_reif_binary_comparison_test<LessThanIff>(proofs, mode, xr,
                        [](int, int c) { return c == 0; });
                else if (mode == "le_iff")
                    run_dup_reif_binary_comparison_test<LessThanEqualIff>(proofs, mode, xr,
                        [](int, int c) { return c == 1; });
                else if (mode == "gt_iff")
                    run_dup_reif_binary_comparison_test<GreaterThanIff>(proofs, mode, xr,
                        [](int, int c) { return c == 0; });
                else if (mode == "ge_iff")
                    run_dup_reif_binary_comparison_test<GreaterThanEqualIff>(proofs, mode, xr,
                        [](int, int c) { return c == 1; });
                // else: lt, gt, lt_if, gt_if — Bucket A/B, no dup test
            }
        }
    }

    return EXIT_SUCCESS;
}
