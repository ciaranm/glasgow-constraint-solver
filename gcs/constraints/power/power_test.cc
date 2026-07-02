#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/power.hh>
#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::pair;
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
    // MiniZinc semantics: 0^0 = 1, and a negative exponent is 1 div a^|b|
    // truncated, so zero for |a| >= 2 and undefined for a = 0.
    auto power_is_satisfying(long long a, long long b, long long c) -> bool
    {
        if (b == 0)
            return c == 1;
        if (a == 1)
            return c == 1;
        if (a == -1)
            return c == ((b % 2 == 0) ? 1 : -1);
        if (b < 0)
            return a != 0 && c == 0;
        if (a == 0)
            return c == 0;
        long long r = 1;
        for (long long i = 0; i < b; ++i) {
            long long next;
            if (__builtin_mul_overflow(r, a, &next))
                return false;
            r = next;
        }
        return r == c;
    }

    auto level_name(const PowerConsistency & level) -> string
    {
        return overloaded{                                              //
            [](const consistency::Auto &) -> string { return "auto"; }, //
            [](const consistency::BC &) -> string { return "bc"; },     //
            [](const consistency::Tabulated &) -> string { return "tabulated"; }}
            .visit(level);
    }
}

// A variable exponent, which goes through the PowerTable fallback and is GAC.
auto run_power_var_exp_test(bool proofs, pair<int, int> base_range, pair<int, int> exp_range, pair<int, int> result_range) -> void
{
    print(cerr, "power var-exp {} {} {} {}", base_range, exp_range, result_range, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    build_expected(expected, [](int a, int b, int c) { return power_is_satisfying(a, b, c); }, base_range, exp_range, result_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(base_range.first), Integer(base_range.second), "b");
    auto v2 = p.create_integer_variable(Integer(exp_range.first), Integer(exp_range.second), "e");
    auto v3 = p.create_integer_variable(Integer(result_range.first), Integer(result_range.second), "r");
    p.post(Power{v1, v2, v3});

    auto proof_name = proofs ? make_optional("power_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});
    check_results(proof_name, expected, actual);
}

// A structurally constant exponent, which dispatches on its value: linear for
// 0 and 1, a Multiply chain for small positive, a case analysis for negative
// or enormous ones.
auto run_power_const_exp_test(bool proofs, const PowerConsistency & level, bool check_gac, pair<int, int> base_range, long long exp,
    pair<int, int> result_range, tuple<int, int, int, int> view_spec = {1, 0, 1, 0}) -> void
{
    const auto & [m1, o1, m3, o3] = view_spec;
    print(cerr, "power {} {} {} ^ {} = {} views {} {}", level_name(level), check_gac ? "gac-checked" : "plain", base_range, exp, result_range,
        view_spec, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int>> expected, actual;

    build_expected(expected, [&](int a, int c) { return power_is_satisfying(m1 * a + o1, exp, m3 * c + o3); }, base_range, result_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(base_range.first), Integer(base_range.second), "b");
    auto v3 = p.create_integer_variable(Integer(result_range.first), Integer(result_range.second), "r");

    auto wrap = [&](SimpleIntegerVariableID v, int m, int o) -> IntegerVariableID {
        IntegerVariableID result = v;
        if (m == -1)
            result = -result;
        return result + Integer{o};
    };
    p.post(Power{wrap(v1, m1, o1), constant_variable(Integer{exp}), wrap(v3, m3, o3), level});

    auto proof_name = proofs ? make_optional("power_test") : nullopt;
    if (check_gac)
        solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v3});
    else
        solve_for_tests(p, proof_name, actual, tuple{v1, v3});
    check_results(proof_name, expected, actual);
}

// Fixed base and exponent, either as singleton variables (the PowerTable
// path) or as a genuine constant exponent (the dispatch paths), pinned to an
// expected unique result or to unsatisfiability.
auto run_power_pinned_test(
    bool proofs, bool exp_is_constant, Integer base, Integer exp, pair<long long, long long> result_range, optional<Integer> expected_result) -> void
{
    print(cerr, "power pinned base={} exp={}{} result_range={} expected={} {}", base, exp, exp_is_constant ? " (constant)" : " (singleton var)",
        result_range, expected_result ? std::to_string(expected_result->raw_value) : "<none>", proofs ? "with proofs:" : ":");
    cerr << flush;

    Problem p;
    auto v1 = p.create_integer_variable(base, base);
    auto v3 = p.create_integer_variable(Integer(result_range.first), Integer(result_range.second));
    if (exp_is_constant)
        p.post(Power{v1, constant_variable(exp), v3});
    else {
        auto v2 = p.create_integer_variable(exp, exp);
        p.post(Power{v1, v2, v3});
    }

    auto proof_name = proofs ? make_optional<string>("power_test") : nullopt;

    set<long long> actual_results;
    solve_with(p,      //
        SolveCallbacks{//
            .solution = [&](const CurrentState & s) -> bool {
                actual_results.insert(s(v3).raw_value);
                return true;
            }},
        proof_name ? std::make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);

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

// A constant base with a view exponent still goes through PowerTable, and
// negative exponents in the view's range now mean zero results, not gaps.
auto run_power_const_base_view_exp_test(bool proofs, int base, pair<int, int> exp_range, int exp_offset, pair<int, int> result_range) -> void
{
    print(cerr, "power constant base {} view exponent {}+{} result {} {}", base, exp_range, exp_offset, result_range, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int>> expected, actual;

    build_expected(expected, [&](int e, int r) { return power_is_satisfying(base, e + exp_offset, r); }, exp_range, result_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto e = p.create_integer_variable(Integer(exp_range.first), Integer(exp_range.second));
    auto r = p.create_integer_variable(Integer(result_range.first), Integer(result_range.second));
    p.post(Power{ConstantIntegerVariableID{Integer{base}}, e + Integer{exp_offset}, r});

    auto proof_name = proofs ? make_optional("power_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{e, r});
    check_results(proof_name, expected, actual);
}

// x ^ 2 = x, an aliased result through the chain.
auto run_power_alias_test(bool proofs, pair<int, int> x_range) -> void
{
    print(cerr, "power alias x^2=x {} {}", x_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    Problem p;
    auto x = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second), "x");
    p.post(Power{x, constant_variable(2_i), x});

    set<tuple<int>> expected, actual;
    build_expected(expected, [](int a) { return power_is_satisfying(a, 2, a); }, x_range);
    println(cerr, " expecting {} solutions", expected.size());

    auto proof_name = proofs ? make_optional("power_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x});
    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<PowerConsistency> levels{consistency::Auto{}, consistency::BC{}, consistency::Tabulated{}};

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        // Variable exponents (PowerTable): including negative exponent values,
        // which now follow the MiniZinc rule.
        run_power_var_exp_test(proofs, {0, 3}, {0, 5}, {-1, 250});
        run_power_var_exp_test(proofs, {-3, 3}, {0, 4}, {-30, 90});
        run_power_var_exp_test(proofs, {2, 4}, {-2, 3}, {-2, 70});
        run_power_var_exp_test(proofs, {-1, 1}, {-3, 3}, {-2, 2});
        run_power_var_exp_test(proofs, {0, 1}, {-2, 3}, {-1, 2});

        for (const auto & level : levels) {
            bool is_bc = holds_alternative<consistency::BC>(level);
            // Constant exponents: 0 and 1 (linear), 2 and 3 (chain; the k = 2
            // case is an aliased Multiply), negative (case analysis), and
            // enormous (case analysis on base in {-1, 0, 1}).
            run_power_const_exp_test(proofs, level, ! is_bc, {-3, 3}, 0, {0, 2});
            run_power_const_exp_test(proofs, level, ! is_bc, {-3, 3}, 1, {-3, 3});
            run_power_const_exp_test(proofs, level, ! is_bc, {-3, 3}, 2, {0, 9});
            run_power_const_exp_test(proofs, level, ! is_bc, {-2, 2}, 3, {-8, 8});
            run_power_const_exp_test(proofs, level, ! is_bc, {-3, 3}, -2, {-2, 2});
            run_power_const_exp_test(proofs, level, ! is_bc, {-2, 2}, 100, {-2, 2});
            run_power_const_exp_test(proofs, level, ! is_bc, {-2, 2}, -3, {-2, 2});

            // Views on the base and the result.
            run_power_const_exp_test(proofs, level, ! is_bc, {-2, 2}, 2, {-1, 8}, {1, 1, 1, -1});
            run_power_const_exp_test(proofs, level, ! is_bc, {1, 3}, 3, {-8, 8}, {-1, 1, 1, 0});
        }

        // Wider domains fall back on the chain without tabulation.
        run_power_const_exp_test(proofs, consistency::Auto{}, false, {-12, 12}, 2, {-10, 150});
        run_power_const_exp_test(proofs, consistency::Auto{}, false, {-6, 6}, 3, {-220, 220});

        run_power_alias_test(proofs, {-5, 5});

        for (bool exp_is_constant : {false, true}) {
            // 9^19 = 1350851717672992089 is exactly representable in long long but
            // is off-by-89 when computed via double-precision pow(); pin the result
            // to a window bracketing both.
            run_power_pinned_test(
                proofs, exp_is_constant, 9_i, 19_i, {1350851717672992000LL, 1350851717672992089LL}, make_optional(Integer{1350851717672992089LL}));

            // 10^20 overflows long long: must be UNSAT, not an overflow error.
            run_power_pinned_test(proofs, exp_is_constant, 10_i, 20_i, {0, 100}, nullopt);

            // Negative exponents follow the MiniZinc rule now: 2^-3 = 0.
            run_power_pinned_test(proofs, exp_is_constant, 2_i, Integer{-3}, {-2, 2}, make_optional(0_i));
            run_power_pinned_test(proofs, exp_is_constant, 1_i, Integer{-5}, {-2, 2}, make_optional(1_i));
            run_power_pinned_test(proofs, exp_is_constant, Integer{-2}, Integer{-1}, {-2, 2}, make_optional(0_i));

            // 0^0 = 1 by convention; 0 to a negative power has no support.
            run_power_pinned_test(proofs, exp_is_constant, 0_i, 0_i, {-2, 2}, make_optional(1_i));
            run_power_pinned_test(proofs, exp_is_constant, 0_i, Integer{-2}, {-2, 2}, nullopt);
        }

        // Constant base with a view exponent, spanning negative exponents.
        run_power_const_base_view_exp_test(proofs, 2, {0, 5}, 1, {0, 64});
        run_power_const_base_view_exp_test(proofs, 2, {0, 5}, 0, {0, 20});
        run_power_const_base_view_exp_test(proofs, 2, {0, 5}, -2, {-2, 8});
    }

    return EXIT_SUCCESS;
}
