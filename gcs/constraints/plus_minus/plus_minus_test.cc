#include <gcs/constraints/innards/constraints_test_utils.hh>
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

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using std::cerr;
using std::flush;
using std::function;
using std::is_same_v;
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
auto run_plus_minus_test(bool proofs, const ViewWrapConfig & view_cfg, V1_ v1_range, V2_ v2_range, V3_ v3_range,
    const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 3);
    visit(
        [&](const auto & v1, const auto & v2, const auto & v3) {
            print(
                cerr, "{} [{}] {} {} {} {}", NameOf<Constraint_>::name, view_wrap_config_label(view_cfg), v1, v2, v3, proofs ? " with proofs:" : ":");
        },
        v1_range, v2_range, v3_range);
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    visit([&](const auto & v1, const auto & v2) { build_expected(expected, is_satisfying, v1, v2, v3_range); }, v1_range, v2_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](const auto & r) { return create_integer_variable_or_constant_with_view(p, r, wraps.at(0)); }, v1_range);
    auto v2 = visit([&](const auto & r) { return create_integer_variable_or_constant_with_view(p, r, wraps.at(1)); }, v2_range);
    auto v3 = visit([&](const auto & r) { return create_integer_variable_or_constant_with_view(p, r, wraps.at(2)); }, v3_range);
    p.post(Constraint_{v1, v2, v3});

    auto proof_name = proofs ? make_optional("plus_minus_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_consistency(
        p, proof_name, expected, actual, tuple{pair{v1, CheckConsistency::None}, pair{v2, CheckConsistency::None}, pair{v3, CheckConsistency::None}});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: post Plus / Minus with the same handle in two
// (or all three) slots. Consistency is intentionally not checked: a
// GAC algorithm for distinct variables doesn't generally yield GAC
// under aliasing, and fixing it per-constraint is out of scope.
// See tmp/duplicate_var_audit.md.
namespace
{
    struct AliasV1V2
    {
    };
    struct AliasV1V3
    {
    };
    struct AliasV2V3
    {
    };
    struct AliasAll
    {
    };
}

template <typename Constraint_, typename AliasPattern_>
auto run_dup_plus_minus_test(bool proofs, AliasPattern_, const string & tag, pair<int, int> a_range, pair<int, int> b_range,
    const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    print(cerr, "{} dup {} {} {} {}", NameOf<Constraint_>::name, tag, a_range, b_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    Problem p;
    auto proof_name = proofs ? make_optional(string{NameOf<Constraint_>::name} + "_test_dup_" + tag) : nullopt;

    if constexpr (is_same_v<AliasPattern_, AliasAll>) {
        // C{a, a, a} — only `a_range` matters; `b_range` ignored.
        set<tuple<int>> expected, actual;
        build_expected(expected, [&](int a) { return is_satisfying(a, a, a); }, a_range);
        println(cerr, " expecting {} solutions", expected.size());

        auto a = p.create_integer_variable(Integer(a_range.first), Integer(a_range.second));
        p.post(Constraint_{a, a, a});

        solve_for_tests(p, proof_name, actual, tuple{a});
        check_results(proof_name, expected, actual);
    }
    else {
        set<tuple<int, int>> expected, actual;
        if constexpr (is_same_v<AliasPattern_, AliasV1V2>)
            build_expected(expected, [&](int a, int b) { return is_satisfying(a, a, b); }, a_range, b_range);
        else if constexpr (is_same_v<AliasPattern_, AliasV1V3>)
            build_expected(expected, [&](int a, int b) { return is_satisfying(a, b, a); }, a_range, b_range);
        else // AliasV2V3
            build_expected(expected, [&](int a, int b) { return is_satisfying(a, b, b); }, a_range, b_range);
        println(cerr, " expecting {} solutions", expected.size());

        auto a = p.create_integer_variable(Integer(a_range.first), Integer(a_range.second));
        auto b = p.create_integer_variable(Integer(b_range.first), Integer(b_range.second));
        if constexpr (is_same_v<AliasPattern_, AliasV1V2>)
            p.post(Constraint_{a, a, b});
        else if constexpr (is_same_v<AliasPattern_, AliasV1V3>)
            p.post(Constraint_{a, b, a});
        else
            p.post(Constraint_{a, b, b});

        solve_for_tests(p, proof_name, actual, tuple{a, b});
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 3;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "plus_minus view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    using V12 = variant<int, pair<int, int>, vector<int>>;
    using V3 = variant<int, pair<int, int>>;
    vector<tuple<V12, V12, V3>> data = {
        {pair{2, 5}, pair{1, 6}, pair{1, 12}},                                  //
        {pair{1, 6}, pair{2, 5}, pair{5, 8}},                                   //
        {pair{1, 3}, pair{1, 3}, pair{0, 10}},                                  //
        {pair{1, 3}, pair{1, 3}, pair{1, 3}},                                   //
        {pair{1, 5}, pair{6, 8}, pair{-10, 10}},                                //
        {pair{1, 1}, pair{2, 4}, pair{-5, 5}},                                  //
        {pair{10, 15}, pair{60, 80}, pair{-100, 100}},                          //
        {pair{-10, 0}, pair{-4, 2}, pair{4, 9}},                                //
        {pair{1, 100}, pair{1, 3}, pair{1, 100}},                               //
        {pair{1, 10}, pair{1, 3}, pair{1, 10}},                                 //
        {pair{1, 10}, pair{1, 10}, pair{1, 20}},                                //
        {vector{1, 5, 10}, vector{1, 5, 10}, pair{1, 20}},                      //
        {vector{1, 2, 3, 5, 6, 10}, vector{1, 2, 3, 5, 8, 9, 10}, pair{1, 20}}, //
        // Constant-result regression: x + y == 6 over [1,5] × [1,5].
        {pair{1, 5}, pair{1, 5}, 6}, //
        // Constant-operand: x + 2 == z over [1,5] × [3,8].
        {pair{1, 5}, 2, pair{3, 8}}, //
        // issue #254: fully all-constant operands (ConstantIntegerVariableID).
        // Each row runs for both Plus and Minus; build_expected gives the
        // per-operation truth, e.g. {2,3,5}: 2+3==5 (Plus SAT) but 2-3!=5
        // (Minus UNSAT); {4,1,3}: 4+1!=3 (Plus UNSAT) but 4-1==3 (Minus SAT).
        {2, 3, 5}, //
        {4, 1, 3}, //
        {0, 0, 0}  //
    };

    // The random sweep mixes constants and bounds-pairs across all three slots
    // via random_bounds_or_constant. v1/v2's variant is wider than the helper's
    // return type (because hand-rolled cases include hole-y vector<int> domains
    // that the random sweep doesn't produce), so visit-widen at insertion.
    auto widen_v12 = [](variant<int, pair<int, int>> v) -> V12 { return visit([](auto x) -> V12 { return x; }, v); };
    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        auto r1 = generate_random_data_item(rand, random_bounds_or_constant(-10, 10, 5, 15));
        auto r2 = generate_random_data_item(rand, random_bounds_or_constant(-10, 10, 5, 15));
        auto r3 = generate_random_data_item(rand, random_bounds_or_constant(-10, 10, 5, 15));
        data.emplace_back(widen_v12(r1), widen_v12(r2), r3);
    }

    // Bare-handle dup ranges. Skipped under the view-wrap sweep.
    vector<pair<pair<int, int>, pair<int, int>>> dup_data = {
        {{0, 5}, {0, 10}},  //
        {{-3, 3}, {-6, 6}}, //
        {{1, 4}, {-5, 5}},  //
        {{0, 0}, {0, 5}}    //
    };

    auto plus_sat = [](int a, int b, int c) { return a + b == c; };
    auto minus_sat = [](int a, int b, int c) { return a - b == c; };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2, r3] : data) {
            run_plus_minus_test<Plus>(proofs, view_cfg, r1, r2, r3, plus_sat);
            run_plus_minus_test<Minus>(proofs, view_cfg, r1, r2, r3, minus_sat);
        }
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions))
            for (auto & [ar, br] : dup_data) {
                run_dup_plus_minus_test<Plus>(proofs, AliasV1V2{}, "v1v2", ar, br, plus_sat);
                run_dup_plus_minus_test<Plus>(proofs, AliasV1V3{}, "v1v3", ar, br, plus_sat);
                run_dup_plus_minus_test<Plus>(proofs, AliasV2V3{}, "v2v3", ar, br, plus_sat);
                run_dup_plus_minus_test<Plus>(proofs, AliasAll{}, "all", ar, br, plus_sat);
                run_dup_plus_minus_test<Minus>(proofs, AliasV1V2{}, "v1v2", ar, br, minus_sat);
                run_dup_plus_minus_test<Minus>(proofs, AliasV1V3{}, "v1v3", ar, br, minus_sat);
                run_dup_plus_minus_test<Minus>(proofs, AliasV2V3{}, "v2v3", ar, br, minus_sat);
                run_dup_plus_minus_test<Minus>(proofs, AliasAll{}, "all", ar, br, minus_sat);
            }
    }

    return EXIT_SUCCESS;
}
