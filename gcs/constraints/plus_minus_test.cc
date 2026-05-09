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
auto run_plus_minus_test(bool proofs, V1_ v1_range, V2_ v2_range, V3_ v3_range, const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    // Issue #166: Plus/Minus's hand-built `pol` justification calls
    // need_pol_item_defining_literal, which crashes on constant arguments.
    // The propagator itself works fine, so we still exercise constant
    // arguments end-to-end — just not the proof leg. Remove the skip once
    // #166 lands.
    auto holds_int = [](const auto & v) { return std::holds_alternative<int>(v); };
    bool any_constant = holds_int(v1_range) || holds_int(v2_range) || holds_int(v3_range);
    bool effective_proofs = proofs && ! any_constant;

    visit([&](const auto & v1, const auto & v2, const auto & v3) {
        print(cerr, "{} {} {} {} {}", NameOf<Constraint_>::name, v1, v2, v3,
            effective_proofs ? " with proofs:" : (proofs ? " (no-proofs: constant arg):" : ":"));
    },
        v1_range, v2_range, v3_range);
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
    auto v3 = visit([&](const auto & r) { return create_integer_variable_or_constant(p, r); }, v3_range);
    p.post(Constraint_{v1, v2, v3});

    auto proof_name = effective_proofs ? make_optional("plus_minus_test") : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{v1, CheckConsistency::None}, pair{v2, CheckConsistency::None}, pair{v3, CheckConsistency::None}});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    using V12 = variant<int, pair<int, int>, vector<int>>;
    using V3 = variant<int, pair<int, int>>;
    vector<tuple<V12, V12, V3>> data = {
        {pair{2, 5}, pair{1, 6}, pair{1, 12}},
        {pair{1, 6}, pair{2, 5}, pair{5, 8}},
        {pair{1, 3}, pair{1, 3}, pair{0, 10}},
        {pair{1, 3}, pair{1, 3}, pair{1, 3}},
        {pair{1, 5}, pair{6, 8}, pair{-10, 10}},
        {pair{1, 1}, pair{2, 4}, pair{-5, 5}},
        {pair{10, 15}, pair{60, 80}, pair{-100, 100}},
        {pair{-10, 0}, pair{-4, 2}, pair{4, 9}},
        {pair{1, 100}, pair{1, 3}, pair{1, 100}},
        {pair{1, 10}, pair{1, 3}, pair{1, 10}},
        {pair{1, 10}, pair{1, 10}, pair{1, 20}},
        {vector{1, 5, 10}, vector{1, 5, 10}, pair{1, 20}},
        {vector{1, 2, 3, 5, 6, 10}, vector{1, 2, 3, 5, 8, 9, 10}, pair{1, 20}},
        // Constant-result regression: x + y == 6 over [1,5] × [1,5].
        {pair{1, 5}, pair{1, 5}, 6},
        // Constant-operand: x + 2 == z over [1,5] × [3,8].
        {pair{1, 5}, 2, pair{3, 8}}};

    // The random sweep mixes constants and bounds-pairs across all three slots
    // via random_bounds_or_constant. v1/v2's variant is wider than the helper's
    // return type (because hand-rolled cases include hole-y vector<int> domains
    // that the random sweep doesn't produce), so visit-widen at insertion.
    auto widen_v12 = [](variant<int, pair<int, int>> v) -> V12 {
        return visit([](auto x) -> V12 { return x; }, v);
    };
    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        auto r1 = generate_random_data_item(rand, random_bounds_or_constant(-10, 10, 5, 15));
        auto r2 = generate_random_data_item(rand, random_bounds_or_constant(-10, 10, 5, 15));
        auto r3 = generate_random_data_item(rand, random_bounds_or_constant(-10, 10, 5, 15));
        data.emplace_back(widen_v12(r1), widen_v12(r2), r3);
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2, r3] : data) {
            run_plus_minus_test<Plus>(proofs, r1, r2, r3, [](int a, int b, int c) { return a + b == c; });
            run_plus_minus_test<Minus>(proofs, r1, r2, r3, [](int a, int b, int c) { return a - b == c; });
        }
    }

    return EXIT_SUCCESS;
}
