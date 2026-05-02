#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/lex.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
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
#endif

using std::cerr;
using std::flush;
using std::make_optional;
using std::nullopt;
using std::pair;
using std::set;
using std::tie;
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

enum class LexVariant
{
    GreaterThan,
    GreaterEqual,
    LessThan,
    LessThanEqual
};

template <LexVariant V, typename T>
auto cmp_lex(const T & a, const T & b) -> bool
{
    if constexpr (V == LexVariant::GreaterThan) return a > b;
    else if constexpr (V == LexVariant::GreaterEqual) return a >= b;
    else if constexpr (V == LexVariant::LessThan) return a < b;
    else return a <= b;
}

template <LexVariant V>
auto post_lex(Problem & p, vector<IntegerVariableID> v1, vector<IntegerVariableID> v2) -> void
{
    if constexpr (V == LexVariant::GreaterThan)
        p.post(LexGreaterThan{std::move(v1), std::move(v2)});
    else if constexpr (V == LexVariant::GreaterEqual)
        p.post(LexGreaterEqual{std::move(v1), std::move(v2)});
    else if constexpr (V == LexVariant::LessThan)
        p.post(LexLessThan{std::move(v1), std::move(v2)});
    else
        p.post(LexLessThanEqual{std::move(v1), std::move(v2)});
}

template <LexVariant V>
auto variant_name() -> const char *
{
    if constexpr (V == LexVariant::GreaterThan) return ">";
    else if constexpr (V == LexVariant::GreaterEqual) return ">=";
    else if constexpr (V == LexVariant::LessThan) return "<";
    else return "<=";
}

template <LexVariant V>
auto run_lex_test_2(bool proofs,
    pair<int, int> r1, pair<int, int> r2,
    pair<int, int> r3, pair<int, int> r4) -> void
{
    print(cerr, "lex 2 [{},{}] [{},{}] {} [{},{}] [{},{}]{}",
        r1.first, r1.second, r2.first, r2.second,
        variant_name<V>(),
        r3.first, r3.second, r4.first, r4.second,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int>> expected, actual;
    build_expected(expected, [](int a1, int a2, int b1, int b2) {
        return cmp_lex<V>(tie(a1, a2), tie(b1, b2));
    }, r1, r2, r3, r4);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    auto v3 = p.create_integer_variable(Integer(r3.first), Integer(r3.second));
    auto v4 = p.create_integer_variable(Integer(r4.first), Integer(r4.second));
    post_lex<V>(p, {v1, v2}, {v3, v4});

    auto proof_name = proofs ? make_optional("lex_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, v4});
    check_results(proof_name, expected, actual);
}

template <LexVariant V>
auto run_lex_test_3(bool proofs,
    pair<int, int> r1, pair<int, int> r2, pair<int, int> r3,
    pair<int, int> r4, pair<int, int> r5, pair<int, int> r6) -> void
{
    print(cerr, "lex 3 [{},{}] [{},{}] [{},{}] {} [{},{}] [{},{}] [{},{}]{}",
        r1.first, r1.second, r2.first, r2.second, r3.first, r3.second,
        variant_name<V>(),
        r4.first, r4.second, r5.first, r5.second, r6.first, r6.second,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int, int, int>> expected, actual;
    build_expected(expected, [](int a1, int a2, int a3, int b1, int b2, int b3) {
        return cmp_lex<V>(tie(a1, a2, a3), tie(b1, b2, b3));
    }, r1, r2, r3, r4, r5, r6);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    auto v3 = p.create_integer_variable(Integer(r3.first), Integer(r3.second));
    auto v4 = p.create_integer_variable(Integer(r4.first), Integer(r4.second));
    auto v5 = p.create_integer_variable(Integer(r5.first), Integer(r5.second));
    auto v6 = p.create_integer_variable(Integer(r6.first), Integer(r6.second));
    post_lex<V>(p, {v1, v2, v3}, {v4, v5, v6});

    auto proof_name = proofs ? make_optional("lex_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, v4, v5, v6});
    check_results(proof_name, expected, actual);
}

template <LexVariant V>
auto run_lex_test_6(bool proofs,
    pair<int, int> r1, pair<int, int> r2, pair<int, int> r3,
    pair<int, int> r4, pair<int, int> r5, pair<int, int> r6,
    pair<int, int> r7, pair<int, int> r8, pair<int, int> r9,
    pair<int, int> r10, pair<int, int> r11, pair<int, int> r12) -> void
{
    print(cerr, "lex 6 ({}) with proofs={}:", variant_name<V>(), proofs);
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [](vector<int> v) {
        return cmp_lex<V>(tie(v[0], v[1], v[2], v[3], v[4], v[5]), tie(v[6], v[7], v[8], v[9], v[10], v[11]));
    }, vector<pair<int, int>>{r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> all_vars;
    for (const auto & r : {r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12})
        all_vars.push_back(p.create_integer_variable(Integer(r.first), Integer(r.second)));

    post_lex<V>(p,
        vector<IntegerVariableID>{all_vars.begin(), all_vars.begin() + 6},
        vector<IntegerVariableID>{all_vars.begin() + 6, all_vars.end()});

    auto proof_name = proofs ? make_optional("lex_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{all_vars});
    check_results(proof_name, expected, actual);
}

template <LexVariant V>
auto run_variant_tests(bool proofs) -> void
{
    // Length-2: same domain for both arrays
    run_lex_test_2<V>(proofs, {1, 3}, {1, 3}, {1, 3}, {1, 3});
    run_lex_test_2<V>(proofs, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Length-2: asymmetric domains — first position dominates
    run_lex_test_2<V>(proofs, {2, 4}, {1, 3}, {1, 3}, {1, 3});

    // Length-2: first positions equal, second position determines order
    run_lex_test_2<V>(proofs, {1, 2}, {1, 3}, {1, 2}, {1, 3});

    // Length-2: vars_1 strictly dominated. Strict variants are unsatisfiable
    // here; non-strict in the same direction is also unsatisfiable.
    run_lex_test_2<V>(proofs, {1, 1}, {1, 2}, {2, 3}, {3, 4});

    // Length-2: negative values
    run_lex_test_2<V>(proofs, {-2, 1}, {-2, 1}, {-2, 1}, {-2, 1});

    // Length-2: larger domain
    run_lex_test_2<V>(proofs, {1, 6}, {1, 6}, {1, 6}, {1, 6});

    // Length-3: same domain for both arrays
    run_lex_test_3<V>(proofs, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {1, 3});
    run_lex_test_3<V>(proofs, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Length-3: asymmetric domains
    run_lex_test_3<V>(proofs, {1, 3}, {1, 2}, {1, 3}, {1, 2}, {1, 3}, {1, 2});

    // Length-3: first two positions equal, third determines order
    run_lex_test_3<V>(proofs, {1, 2}, {1, 2}, {1, 3}, {1, 2}, {1, 2}, {1, 3});

    // Length-3 GAC: middle position prefix-blocks witnesses past it. For
    // strict, this forces vars_1[0] strictly larger than vars_2[0]. For
    // non-strict, this also forces strict at 0 (since the equal-prefix
    // can't extend through the prefix block).
    run_lex_test_3<V>(proofs, {1, 2}, {1, 1}, {1, 2}, {1, 2}, {2, 2}, {1, 2});

    // Length-3: larger domain
    run_lex_test_3<V>(proofs, {1, 5}, {1, 5}, {1, 5}, {1, 5}, {1, 5}, {1, 5});

    // Length-6 with small domains, to exercise longer chains
    run_lex_test_6<V>(proofs,
        {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2},
        {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2});
}

auto run_all_tests(bool proofs) -> void
{
    run_variant_tests<LexVariant::GreaterThan>(proofs);
    run_variant_tests<LexVariant::GreaterEqual>(proofs);
    run_variant_tests<LexVariant::LessThan>(proofs);
    run_variant_tests<LexVariant::LessThanEqual>(proofs);
}

auto main(int, char *[]) -> int
{
    run_all_tests(false);

    if (can_run_veripb())
        run_all_tests(true);

    return EXIT_SUCCESS;
}
