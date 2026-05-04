#include <gcs/constraints/innards/constraints_test_utils.hh>
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
auto run_lex_test_unequal(bool proofs,
    vector<pair<int, int>> r_left,
    vector<pair<int, int>> r_right) -> void
{
    print(cerr, "lex unequal len {} {} len {}{}",
        r_left.size(), variant_name<V>(), r_right.size(),
        proofs ? " with proofs:" : ":");
    cerr << flush;

    auto n_left = r_left.size();
    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [n_left](vector<int> v) {
        vector<int> left(v.begin(), v.begin() + n_left);
        vector<int> right(v.begin() + n_left, v.end());
        return cmp_lex<V>(left, right);
    }, [&]() {
        vector<pair<int, int>> all = r_left;
        all.insert(all.end(), r_right.begin(), r_right.end());
        return all;
    }());
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> all_vars;
    for (const auto & r : r_left)
        all_vars.push_back(p.create_integer_variable(Integer(r.first), Integer(r.second)));
    for (const auto & r : r_right)
        all_vars.push_back(p.create_integer_variable(Integer(r.first), Integer(r.second)));

    post_lex<V>(p,
        vector<IntegerVariableID>{all_vars.begin(), all_vars.begin() + n_left},
        vector<IntegerVariableID>{all_vars.begin() + n_left, all_vars.end()});

    auto proof_name = proofs ? make_optional("lex_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{all_vars});
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

enum class ReifKind
{
    If,
    Iff
};

template <LexVariant V, ReifKind R>
auto post_reified_lex(Problem & p, vector<IntegerVariableID> v1, vector<IntegerVariableID> v2,
    IntegerVariableCondition cond) -> void
{
    if constexpr (R == ReifKind::If) {
        if constexpr (V == LexVariant::GreaterThan)
            p.post(LexGreaterThanIf{std::move(v1), std::move(v2), cond});
        else if constexpr (V == LexVariant::GreaterEqual)
            p.post(LexGreaterEqualIf{std::move(v1), std::move(v2), cond});
        else if constexpr (V == LexVariant::LessThan)
            p.post(LexLessThanIf{std::move(v1), std::move(v2), cond});
        else
            p.post(LexLessThanEqualIf{std::move(v1), std::move(v2), cond});
    }
    else {
        if constexpr (V == LexVariant::GreaterThan)
            p.post(LexGreaterThanIff{std::move(v1), std::move(v2), cond});
        else if constexpr (V == LexVariant::GreaterEqual)
            p.post(LexGreaterEqualIff{std::move(v1), std::move(v2), cond});
        else if constexpr (V == LexVariant::LessThan)
            p.post(LexLessThanIff{std::move(v1), std::move(v2), cond});
        else
            p.post(LexLessThanEqualIff{std::move(v1), std::move(v2), cond});
    }
}

template <ReifKind R>
auto reif_kind_name() -> const char *
{
    if constexpr (R == ReifKind::If) return "if";
    else return "iff";
}

template <LexVariant V, ReifKind R>
auto run_lex_reified_test_2(bool proofs,
    pair<int, int> r1, pair<int, int> r2,
    pair<int, int> r3, pair<int, int> r4) -> void
{
    print(cerr, "lex 2 [{},{}] [{},{}] {} {} [{},{}] [{},{}]{}",
        r1.first, r1.second, r2.first, r2.second,
        variant_name<V>(), reif_kind_name<R>(),
        r3.first, r3.second, r4.first, r4.second,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int, int>> expected, actual;
    // Tuple is (a1, a2, b1, b2, cond_value).
    build_expected(expected, [](int a1, int a2, int b1, int b2, int c) {
        bool constraint_holds = cmp_lex<V>(tie(a1, a2), tie(b1, b2));
        if constexpr (R == ReifKind::If)
            return (c == 0) || constraint_holds;
        else
            return (c == 1) == constraint_holds;
    }, r1, r2, r3, r4, pair{0, 1});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    auto v3 = p.create_integer_variable(Integer(r3.first), Integer(r3.second));
    auto v4 = p.create_integer_variable(Integer(r4.first), Integer(r4.second));
    auto c = p.create_integer_variable(0_i, 1_i);
    post_reified_lex<V, R>(p, {v1, v2}, {v3, v4}, c == 1_i);

    auto proof_name = proofs ? make_optional("lex_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3, v4, c});
    check_results(proof_name, expected, actual);
}

template <LexVariant V, ReifKind R>
auto run_lex_reified_test_3(bool proofs,
    pair<int, int> r1, pair<int, int> r2, pair<int, int> r3,
    pair<int, int> r4, pair<int, int> r5, pair<int, int> r6) -> void
{
    print(cerr, "lex 3 [{},{}] [{},{}] [{},{}] {} {} [{},{}] [{},{}] [{},{}]{}",
        r1.first, r1.second, r2.first, r2.second, r3.first, r3.second,
        variant_name<V>(), reif_kind_name<R>(),
        r4.first, r4.second, r5.first, r5.second, r6.first, r6.second,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int, int, int, int>> expected, actual;
    build_expected(expected, [](int a1, int a2, int a3, int b1, int b2, int b3, int c) {
        bool constraint_holds = cmp_lex<V>(tie(a1, a2, a3), tie(b1, b2, b3));
        if constexpr (R == ReifKind::If)
            return (c == 0) || constraint_holds;
        else
            return (c == 1) == constraint_holds;
    }, r1, r2, r3, r4, r5, r6, pair{0, 1});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    auto v3 = p.create_integer_variable(Integer(r3.first), Integer(r3.second));
    auto v4 = p.create_integer_variable(Integer(r4.first), Integer(r4.second));
    auto v5 = p.create_integer_variable(Integer(r5.first), Integer(r5.second));
    auto v6 = p.create_integer_variable(Integer(r6.first), Integer(r6.second));
    auto c = p.create_integer_variable(0_i, 1_i);
    post_reified_lex<V, R>(p, {v1, v2, v3}, {v4, v5, v6}, c == 1_i);

    auto proof_name = proofs ? make_optional("lex_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3, v4, v5, v6, c});
    check_results(proof_name, expected, actual);
}

template <LexVariant V, ReifKind R>
auto run_lex_reified_test_unequal(bool proofs,
    vector<pair<int, int>> r_left,
    vector<pair<int, int>> r_right) -> void
{
    print(cerr, "lex unequal len {} {} {} len {}{}",
        r_left.size(), variant_name<V>(), reif_kind_name<R>(), r_right.size(),
        proofs ? " with proofs:" : ":");
    cerr << flush;

    auto n_left = r_left.size();
    auto n_right = r_right.size();
    set<tuple<vector<int>, int>> expected, actual;
    build_expected(expected, [n_left, n_right](vector<int> v, int c) {
        vector<int> left(v.begin(), v.begin() + n_left);
        vector<int> right(v.begin() + n_left, v.begin() + n_left + n_right);
        bool constraint_holds = cmp_lex<V>(left, right);
        if constexpr (R == ReifKind::If)
            return (c == 0) || constraint_holds;
        else
            return (c == 1) == constraint_holds;
    }, [&]() {
        vector<pair<int, int>> all = r_left;
        all.insert(all.end(), r_right.begin(), r_right.end());
        return all;
    }(), pair{0, 1});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> all_vars;
    for (const auto & r : r_left)
        all_vars.push_back(p.create_integer_variable(Integer(r.first), Integer(r.second)));
    for (const auto & r : r_right)
        all_vars.push_back(p.create_integer_variable(Integer(r.first), Integer(r.second)));
    auto c = p.create_integer_variable(0_i, 1_i);
    post_reified_lex<V, R>(p,
        vector<IntegerVariableID>{all_vars.begin(), all_vars.begin() + n_left},
        vector<IntegerVariableID>{all_vars.begin() + n_left, all_vars.end()},
        c == 1_i);

    auto proof_name = proofs ? make_optional("lex_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{all_vars, c});
    check_results(proof_name, expected, actual);
}

template <LexVariant V, ReifKind R>
auto run_reified_variant_tests(bool proofs) -> void
{
    // Same domain length 2: exercises must-hold (cond=TRUE) path for some
    // assignments and must-not-hold (cond=FALSE) for others.
    run_lex_reified_test_2<V, R>(proofs, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Asymmetric: at first position vars_1 dominates -> constraint forced
    // hold/fail in some directions.
    run_lex_reified_test_2<V, R>(proofs, {2, 4}, {1, 3}, {1, 3}, {1, 3});

    // Unsat-for-strict: vars_2 strictly dominates vars_1.
    run_lex_reified_test_2<V, R>(proofs, {1, 1}, {1, 2}, {2, 3}, {3, 4});

    // Length-3: prefix-blocking case to test strict force-strict path.
    run_lex_reified_test_3<V, R>(proofs,
        {1, 2}, {1, 1}, {1, 2}, {1, 2}, {2, 2}, {1, 2});

    // Length-3: same domain larger search space.
    run_lex_reified_test_3<V, R>(proofs,
        {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Unequal lengths, both directions, exercising the cond-inference path
    // when the common prefix can be forced equal but lengths differ.
    run_lex_reified_test_unequal<V, R>(proofs, {{1, 2}, {1, 2}}, {{1, 2}, {1, 2}, {1, 2}});
    run_lex_reified_test_unequal<V, R>(proofs, {{1, 2}, {1, 2}, {1, 2}}, {{1, 2}, {1, 2}});
    run_lex_reified_test_unequal<V, R>(proofs, {{1, 3}}, {{1, 3}, {1, 3}});
    run_lex_reified_test_unequal<V, R>(proofs, {{1, 3}, {1, 3}}, {{1, 3}});
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

    // Unequal lengths: standard lex semantics says longer wins on equal
    // common prefix. So [1,2] <_lex [1,2,0] holds and [1,2,0] <=_lex [1,2]
    // does not. Cover both directions and several common-prefix shapes.
    run_lex_test_unequal<V>(proofs, {{1, 2}, {1, 2}}, {{1, 2}, {1, 2}, {1, 2}});
    run_lex_test_unequal<V>(proofs, {{1, 2}, {1, 2}, {1, 2}}, {{1, 2}, {1, 2}});

    // Asymmetric domains so the longer side cannot necessarily extend the
    // equal prefix freely.
    run_lex_test_unequal<V>(proofs, {{1, 3}, {1, 2}}, {{1, 3}, {1, 2}, {0, 2}});
    run_lex_test_unequal<V>(proofs, {{1, 3}, {1, 2}, {0, 2}}, {{1, 3}, {1, 2}});

    // Length 1 vs length 3: degenerate "all common prefix is just the first
    // element" case.
    run_lex_test_unequal<V>(proofs, {{1, 3}}, {{1, 3}, {1, 3}, {1, 3}});
    run_lex_test_unequal<V>(proofs, {{1, 3}, {1, 3}, {1, 3}}, {{1, 3}});
}

auto run_all_tests(bool proofs) -> void
{
    run_variant_tests<LexVariant::GreaterThan>(proofs);
    run_variant_tests<LexVariant::GreaterEqual>(proofs);
    run_variant_tests<LexVariant::LessThan>(proofs);
    run_variant_tests<LexVariant::LessThanEqual>(proofs);

    run_reified_variant_tests<LexVariant::GreaterThan, ReifKind::If>(proofs);
    run_reified_variant_tests<LexVariant::GreaterThan, ReifKind::Iff>(proofs);
    run_reified_variant_tests<LexVariant::GreaterEqual, ReifKind::If>(proofs);
    run_reified_variant_tests<LexVariant::GreaterEqual, ReifKind::Iff>(proofs);
    run_reified_variant_tests<LexVariant::LessThan, ReifKind::If>(proofs);
    run_reified_variant_tests<LexVariant::LessThan, ReifKind::Iff>(proofs);
    run_reified_variant_tests<LexVariant::LessThanEqual, ReifKind::If>(proofs);
    run_reified_variant_tests<LexVariant::LessThanEqual, ReifKind::Iff>(proofs);
}

auto main(int, char *[]) -> int
{
    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs);
    }

    return EXIT_SUCCESS;
}
