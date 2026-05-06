#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
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
using std::optional;
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::tuple;
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
    struct NameOf<PlusGAC>
    {
        static const constexpr auto name = "plusgac";
    };

    template <>
    struct NameOf<MinusGAC>
    {
        static const constexpr auto name = "minusgac";
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

    template <>
    struct NameOf<Power>
    {
        static const constexpr auto name = "power";
    };

    auto power_is_satisfying = [](int a, int b, int c) -> bool {
        if (b == 0) return c == 1;
        if (a == 1) return c == 1;
        if (a == -1) return c == ((b % 2 == 0) ? 1 : -1);
        if (b < 0) return false;
        if (a == 0) return c == 0;
        long long r = 1;
        for (int i = 0; i < b; ++i) {
            long long next;
            if (__builtin_mul_overflow(r, static_cast<long long>(a), &next)) return false;
            r = next;
        }
        return r == c;
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

auto run_power_pinned_test(bool proofs, Integer base, Integer exp, pair<long long, long long> result_range, optional<Integer> expected_result) -> void
{
    print(cerr, "arithmetic power pinned base={} exp={} result_range={} expected={} {}",
        base, exp, result_range, expected_result ? std::to_string(expected_result->raw_value) : "<none>",
        proofs ? "with proofs:" : ":");
    cerr << flush;

    Problem p;
    auto v1 = p.create_integer_variable(base, base);
    auto v2 = p.create_integer_variable(exp, exp);
    auto v3 = p.create_integer_variable(Integer(result_range.first), Integer(result_range.second));
    p.post(Power{v1, v2, v3});

    auto proof_name = proofs ? make_optional<string>("arithmetic_test") : nullopt;

    set<long long> actual_results;
    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                actual_results.insert(s(v3).raw_value);
                return true;
            }},
        proof_name ? std::make_optional<ProofOptions>(ProofFileNames{*proof_name}, true, false) : nullopt);

    println(cerr, " got {} solutions", actual_results.size());

    if (expected_result) {
        if (actual_results.size() != 1 || *actual_results.begin() != expected_result->raw_value) {
            println(cerr, "expected solution {}, got {}", expected_result->raw_value, actual_results);
            throw UnexpectedException{"power pinned test produced wrong result"};
        }
    }
    else {
        if (! actual_results.empty()) {
            println(cerr, "expected no solutions, got {}", actual_results);
            throw UnexpectedException{"power pinned test produced unexpected solutions"};
        }
    }

    if (proof_name)
        if (! run_veripb(*proof_name + ".opb", *proof_name + ".pbp"))
            throw UnexpectedException{"veripb verification failed"};
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

    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>>> power_data = {
        {{0, 3}, {0, 5}, {-1, 250}},
        {{2, 4}, {0, 4}, {0, 260}},
        {{-3, 3}, {0, 4}, {-30, 90}},
        {{1, 1}, {-3, 3}, {-2, 2}},
        {{-1, 1}, {-3, 3}, {-2, 2}},
        {{0, 1}, {-2, 3}, {-1, 2}},
        {{2, 5}, {-1, 4}, {-5, 700}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2, r3] : data) {
            run_arithmetic_test<PlusGAC>(proofs, r1, r2, r3, [](int a, int b, int c) { return a + b == c; });
            run_arithmetic_test<MinusGAC>(proofs, r1, r2, r3, [](int a, int b, int c) { return a - b == c; });
            run_arithmetic_test<Times>(proofs, r1, r2, r3, [](int a, int b, int c) { return a * b == c; });
            run_arithmetic_test<Div>(proofs, r1, r2, r3, [](int a, int b, int c) { return 0 != b && a / b == c; });
            run_arithmetic_test<Mod>(proofs, r1, r2, r3, [](int a, int b, int c) { return 0 != b && a % b == c; });
        }
        for (auto & [r1, r2, r3] : power_data) {
            run_arithmetic_test<Power>(proofs, r1, r2, r3, power_is_satisfying);
        }

        // 9^19 = 1350851717672992089 is exactly representable in long long but is
        // off-by-89 when computed via double-precision pow(); the previous bug
        // produced 1350851717672992000.  Pin the result variable to a 90-value
        // window bracketing both, so this exercises the bug without expanding
        // GACArithmetic's tuple table.
        run_power_pinned_test(proofs, 9_i, 19_i, {1350851717672992000LL, 1350851717672992089LL}, make_optional(Integer{1350851717672992089LL}));

        // 10^20 overflows long long.  Constraint must be UNSAT.
        run_power_pinned_test(proofs, 10_i, 20_i, {0, 100}, nullopt);

        // Negative exponent with |base| != 1: no integer answer, so UNSAT.
        run_power_pinned_test(proofs, 2_i, Integer{-3}, {-2, 2}, nullopt);

        // 1^n = 1 for all integer n, including negative.
        run_power_pinned_test(proofs, 1_i, Integer{-5}, {-2, 2}, make_optional(1_i));

        // 0^0 = 1 by convention.
        run_power_pinned_test(proofs, 0_i, 0_i, {-2, 2}, make_optional(1_i));
    }

    return EXIT_SUCCESS;
}
