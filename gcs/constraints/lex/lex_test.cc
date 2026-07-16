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
using std::string;
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
    if constexpr (V == LexVariant::GreaterThan)
        return a > b;
    else if constexpr (V == LexVariant::GreaterEqual)
        return a >= b;
    else if constexpr (V == LexVariant::LessThan)
        return a < b;
    else
        return a <= b;
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
    if constexpr (V == LexVariant::GreaterThan)
        return ">";
    else if constexpr (V == LexVariant::GreaterEqual)
        return ">=";
    else if constexpr (V == LexVariant::LessThan)
        return "<";
    else
        return "<=";
}

template <LexVariant V>
auto run_lex_test_2(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, pair<int, int> r4) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 4);
    print(cerr, "lex 2 [{}] [{},{}] [{},{}] {} [{},{}] [{},{}]{}", view_wrap_config_label(view_cfg), r1.first, r1.second, r2.first, r2.second,
        variant_name<V>(), r3.first, r3.second, r4.first, r4.second, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int>> expected, actual;
    build_expected(expected, [](int a1, int a2, int b1, int b2) { return cmp_lex<V>(tie(a1, a2), tie(b1, b2)); }, r1, r2, r3, r4);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, r1, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, r2, wraps.at(1));
    auto v3 = create_integer_variable_or_constant_with_view(p, r3, wraps.at(2));
    auto v4 = create_integer_variable_or_constant_with_view(p, r4, wraps.at(3));
    post_lex<V>(p, {v1, v2}, {v3, v4});

    auto proof_name = proofs ? make_optional("lex_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, v4});
    check_results(proof_name, expected, actual);
}

template <LexVariant V>
auto run_lex_test_3(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, pair<int, int> r4,
    pair<int, int> r5, pair<int, int> r6) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 6);
    print(cerr, "lex 3 [{}] [{},{}] [{},{}] [{},{}] {} [{},{}] [{},{}] [{},{}]{}", view_wrap_config_label(view_cfg), r1.first, r1.second, r2.first,
        r2.second, r3.first, r3.second, variant_name<V>(), r4.first, r4.second, r5.first, r5.second, r6.first, r6.second,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int, int, int>> expected, actual;
    build_expected(
        expected, [](int a1, int a2, int a3, int b1, int b2, int b3) { return cmp_lex<V>(tie(a1, a2, a3), tie(b1, b2, b3)); }, r1, r2, r3, r4, r5,
        r6);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, r1, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, r2, wraps.at(1));
    auto v3 = create_integer_variable_or_constant_with_view(p, r3, wraps.at(2));
    auto v4 = create_integer_variable_or_constant_with_view(p, r4, wraps.at(3));
    auto v5 = create_integer_variable_or_constant_with_view(p, r5, wraps.at(4));
    auto v6 = create_integer_variable_or_constant_with_view(p, r6, wraps.at(5));
    post_lex<V>(p, {v1, v2, v3}, {v4, v5, v6});

    auto proof_name = proofs ? make_optional("lex_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, v4, v5, v6});
    check_results(proof_name, expected, actual);
}

template <LexVariant V>
auto run_lex_test_unequal(bool proofs, const ViewWrapConfig & view_cfg, vector<pair<int, int>> r_left, vector<pair<int, int>> r_right) -> void
{
    auto wraps = wraps_for_positions(view_cfg, static_cast<int>(r_left.size() + r_right.size()));
    print(cerr, "lex unequal [{}] len {} {} len {}{}", view_wrap_config_label(view_cfg), r_left.size(), variant_name<V>(), r_right.size(),
        proofs ? " with proofs:" : ":");
    cerr << flush;

    auto n_left = r_left.size();
    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [n_left](vector<int> v) {
            vector<int> left(v.begin(), v.begin() + n_left);
            vector<int> right(v.begin() + n_left, v.end());
            return cmp_lex<V>(left, right);
        },
        [&]() {
            vector<pair<int, int>> all = r_left;
            all.insert(all.end(), r_right.begin(), r_right.end());
            return all;
        }());
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> all_vars;
    for (const auto & r : r_left)
        all_vars.push_back(create_integer_variable_or_constant_with_view(p, r, wraps.at(all_vars.size())));
    for (const auto & r : r_right)
        all_vars.push_back(create_integer_variable_or_constant_with_view(p, r, wraps.at(all_vars.size())));

    post_lex<V>(p, vector<IntegerVariableID>{all_vars.begin(), all_vars.begin() + n_left},
        vector<IntegerVariableID>{all_vars.begin() + n_left, all_vars.end()});

    auto proof_name = proofs ? make_optional("lex_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{all_vars});
    check_results(proof_name, expected, actual);
}

template <LexVariant V>
auto run_lex_test_6(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, pair<int, int> r4,
    pair<int, int> r5, pair<int, int> r6, pair<int, int> r7, pair<int, int> r8, pair<int, int> r9, pair<int, int> r10, pair<int, int> r11,
    pair<int, int> r12) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 12);
    print(cerr, "lex 6 [{}] ({}) with proofs={}:", view_wrap_config_label(view_cfg), variant_name<V>(), proofs);
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected, [](vector<int> v) { return cmp_lex<V>(tie(v[0], v[1], v[2], v[3], v[4], v[5]), tie(v[6], v[7], v[8], v[9], v[10], v[11])); },
        vector<pair<int, int>>{r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> all_vars;
    for (const auto & r : {r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12})
        all_vars.push_back(create_integer_variable_or_constant_with_view(p, r, wraps.at(all_vars.size())));

    post_lex<V>(
        p, vector<IntegerVariableID>{all_vars.begin(), all_vars.begin() + 6}, vector<IntegerVariableID>{all_vars.begin() + 6, all_vars.end()});

    auto proof_name = proofs ? make_optional("lex_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{all_vars});
    check_results(proof_name, expected, actual);
}

enum class ReifKind
{
    If,
    Iff
};

template <LexVariant V, ReifKind R>
auto post_reified_lex(Problem & p, vector<IntegerVariableID> v1, vector<IntegerVariableID> v2, IntegerVariableCondition cond) -> void
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
    if constexpr (R == ReifKind::If)
        return "if";
    else
        return "iff";
}

template <LexVariant V, ReifKind R>
auto run_lex_reified_test_2(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, pair<int, int> r4)
    -> void
{
    auto wraps = wraps_for_positions(view_cfg, 4);
    print(cerr, "lex 2 [{}] [{},{}] [{},{}] {} {} [{},{}] [{},{}]{}", view_wrap_config_label(view_cfg), r1.first, r1.second, r2.first, r2.second,
        variant_name<V>(), reif_kind_name<R>(), r3.first, r3.second, r4.first, r4.second, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int, int>> expected, actual;
    // Tuple is (a1, a2, b1, b2, cond_value).
    build_expected(
        expected,
        [](int a1, int a2, int b1, int b2, int c) {
            bool constraint_holds = cmp_lex<V>(tie(a1, a2), tie(b1, b2));
            if constexpr (R == ReifKind::If)
                return (c == 0) || constraint_holds;
            else
                return (c == 1) == constraint_holds;
        },
        r1, r2, r3, r4, pair{0, 1});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, r1, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, r2, wraps.at(1));
    auto v3 = create_integer_variable_or_constant_with_view(p, r3, wraps.at(2));
    auto v4 = create_integer_variable_or_constant_with_view(p, r4, wraps.at(3));
    auto c = p.create_integer_variable(0_i, 1_i);
    post_reified_lex<V, R>(p, {v1, v2}, {v3, v4}, c == 1_i);

    auto proof_name = proofs ? make_optional("lex_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3, v4, c});
    check_results(proof_name, expected, actual);
}

template <LexVariant V, ReifKind R>
auto run_lex_reified_test_3(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, pair<int, int> r4,
    pair<int, int> r5, pair<int, int> r6) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 6);
    print(cerr, "lex 3 [{}] [{},{}] [{},{}] [{},{}] {} {} [{},{}] [{},{}] [{},{}]{}", view_wrap_config_label(view_cfg), r1.first, r1.second, r2.first,
        r2.second, r3.first, r3.second, variant_name<V>(), reif_kind_name<R>(), r4.first, r4.second, r5.first, r5.second, r6.first, r6.second,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int, int, int, int>> expected, actual;
    build_expected(
        expected,
        [](int a1, int a2, int a3, int b1, int b2, int b3, int c) {
            bool constraint_holds = cmp_lex<V>(tie(a1, a2, a3), tie(b1, b2, b3));
            if constexpr (R == ReifKind::If)
                return (c == 0) || constraint_holds;
            else
                return (c == 1) == constraint_holds;
        },
        r1, r2, r3, r4, r5, r6, pair{0, 1});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, r1, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, r2, wraps.at(1));
    auto v3 = create_integer_variable_or_constant_with_view(p, r3, wraps.at(2));
    auto v4 = create_integer_variable_or_constant_with_view(p, r4, wraps.at(3));
    auto v5 = create_integer_variable_or_constant_with_view(p, r5, wraps.at(4));
    auto v6 = create_integer_variable_or_constant_with_view(p, r6, wraps.at(5));
    auto c = p.create_integer_variable(0_i, 1_i);
    post_reified_lex<V, R>(p, {v1, v2, v3}, {v4, v5, v6}, c == 1_i);

    auto proof_name = proofs ? make_optional("lex_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3, v4, v5, v6, c});
    check_results(proof_name, expected, actual);
}

template <LexVariant V, ReifKind R>
auto run_lex_reified_test_unequal(bool proofs, const ViewWrapConfig & view_cfg, vector<pair<int, int>> r_left, vector<pair<int, int>> r_right) -> void
{
    auto wraps = wraps_for_positions(view_cfg, static_cast<int>(r_left.size() + r_right.size()));
    print(cerr, "lex unequal [{}] len {} {} {} len {}{}", view_wrap_config_label(view_cfg), r_left.size(), variant_name<V>(), reif_kind_name<R>(),
        r_right.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    auto n_left = r_left.size();
    auto n_right = r_right.size();
    set<tuple<vector<int>, int>> expected, actual;
    build_expected(
        expected,
        [n_left, n_right](vector<int> v, int c) {
            vector<int> left(v.begin(), v.begin() + n_left);
            vector<int> right(v.begin() + n_left, v.begin() + n_left + n_right);
            bool constraint_holds = cmp_lex<V>(left, right);
            if constexpr (R == ReifKind::If)
                return (c == 0) || constraint_holds;
            else
                return (c == 1) == constraint_holds;
        },
        [&]() {
            vector<pair<int, int>> all = r_left;
            all.insert(all.end(), r_right.begin(), r_right.end());
            return all;
        }(),
        pair{0, 1});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> all_vars;
    for (const auto & r : r_left)
        all_vars.push_back(create_integer_variable_or_constant_with_view(p, r, wraps.at(all_vars.size())));
    for (const auto & r : r_right)
        all_vars.push_back(create_integer_variable_or_constant_with_view(p, r, wraps.at(all_vars.size())));
    auto c = p.create_integer_variable(0_i, 1_i);
    post_reified_lex<V, R>(p, vector<IntegerVariableID>{all_vars.begin(), all_vars.begin() + n_left},
        vector<IntegerVariableID>{all_vars.begin() + n_left, all_vars.end()}, c == 1_i);

    auto proof_name = proofs ? make_optional("lex_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{all_vars, c});
    check_results(proof_name, expected, actual);
}

template <LexVariant V, ReifKind R>
auto run_reified_variant_tests(bool proofs, const ViewWrapConfig & view_cfg) -> void
{
    // Same domain length 2: exercises must-hold (cond=TRUE) path for some
    // assignments and must-not-hold (cond=FALSE) for others.
    run_lex_reified_test_2<V, R>(proofs, view_cfg, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Asymmetric: at first position vars_1 dominates -> constraint forced
    // hold/fail in some directions.
    run_lex_reified_test_2<V, R>(proofs, view_cfg, {2, 4}, {1, 3}, {1, 3}, {1, 3});

    // Unsat-for-strict: vars_2 strictly dominates vars_1.
    run_lex_reified_test_2<V, R>(proofs, view_cfg, {1, 1}, {1, 2}, {2, 3}, {3, 4});

    // Length-3: prefix-blocking case to test strict force-strict path.
    run_lex_reified_test_3<V, R>(proofs, view_cfg, {1, 2}, {1, 1}, {1, 2}, {1, 2}, {2, 2}, {1, 2});

    // Length-3: same domain larger search space.
    run_lex_reified_test_3<V, R>(proofs, view_cfg, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Unequal lengths, both directions, exercising the cond-inference path
    // when the common prefix can be forced equal but lengths differ.
    run_lex_reified_test_unequal<V, R>(proofs, view_cfg, {{1, 2}, {1, 2}}, {{1, 2}, {1, 2}, {1, 2}});
    run_lex_reified_test_unequal<V, R>(proofs, view_cfg, {{1, 2}, {1, 2}, {1, 2}}, {{1, 2}, {1, 2}});
    run_lex_reified_test_unequal<V, R>(proofs, view_cfg, {{1, 3}}, {{1, 3}, {1, 3}});
    run_lex_reified_test_unequal<V, R>(proofs, view_cfg, {{1, 3}, {1, 3}}, {{1, 3}});
}

template <LexVariant V>
auto run_variant_tests(bool proofs, const ViewWrapConfig & view_cfg) -> void
{
    // Length-2: same domain for both arrays
    run_lex_test_2<V>(proofs, view_cfg, {1, 3}, {1, 3}, {1, 3}, {1, 3});
    run_lex_test_2<V>(proofs, view_cfg, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Length-2: asymmetric domains — first position dominates
    run_lex_test_2<V>(proofs, view_cfg, {2, 4}, {1, 3}, {1, 3}, {1, 3});

    // Length-2: first positions equal, second position determines order
    run_lex_test_2<V>(proofs, view_cfg, {1, 2}, {1, 3}, {1, 2}, {1, 3});

    // Length-2: vars_1 strictly dominated. Strict variants are unsatisfiable
    // here; non-strict in the same direction is also unsatisfiable.
    run_lex_test_2<V>(proofs, view_cfg, {1, 1}, {1, 2}, {2, 3}, {3, 4});

    // Length-2: negative values
    run_lex_test_2<V>(proofs, view_cfg, {-2, 1}, {-2, 1}, {-2, 1}, {-2, 1});

    // Length-2: larger domain
    run_lex_test_2<V>(proofs, view_cfg, {1, 6}, {1, 6}, {1, 6}, {1, 6});

    // Length-3: same domain for both arrays
    run_lex_test_3<V>(proofs, view_cfg, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {1, 3});
    run_lex_test_3<V>(proofs, view_cfg, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Length-3: asymmetric domains
    run_lex_test_3<V>(proofs, view_cfg, {1, 3}, {1, 2}, {1, 3}, {1, 2}, {1, 3}, {1, 2});

    // Length-3: first two positions equal, third determines order
    run_lex_test_3<V>(proofs, view_cfg, {1, 2}, {1, 2}, {1, 3}, {1, 2}, {1, 2}, {1, 3});

    // Length-3 GAC: middle position prefix-blocks witnesses past it. For
    // strict, this forces vars_1[0] strictly larger than vars_2[0]. For
    // non-strict, this also forces strict at 0 (since the equal-prefix
    // can't extend through the prefix block).
    run_lex_test_3<V>(proofs, view_cfg, {1, 2}, {1, 1}, {1, 2}, {1, 2}, {2, 2}, {1, 2});

    // Length-3: larger domain
    run_lex_test_3<V>(proofs, view_cfg, {1, 5}, {1, 5}, {1, 5}, {1, 5}, {1, 5}, {1, 5});

    // Length-6 with small domains, to exercise longer chains
    run_lex_test_6<V>(proofs, view_cfg, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Unequal lengths: standard lex semantics says longer wins on equal
    // common prefix. So [1,2] <_lex [1,2,0] holds and [1,2,0] <=_lex [1,2]
    // does not. Cover both directions and several common-prefix shapes.
    run_lex_test_unequal<V>(proofs, view_cfg, {{1, 2}, {1, 2}}, {{1, 2}, {1, 2}, {1, 2}});
    run_lex_test_unequal<V>(proofs, view_cfg, {{1, 2}, {1, 2}, {1, 2}}, {{1, 2}, {1, 2}});

    // Asymmetric domains so the longer side cannot necessarily extend the
    // equal prefix freely.
    run_lex_test_unequal<V>(proofs, view_cfg, {{1, 3}, {1, 2}}, {{1, 3}, {1, 2}, {0, 2}});
    run_lex_test_unequal<V>(proofs, view_cfg, {{1, 3}, {1, 2}, {0, 2}}, {{1, 3}, {1, 2}});

    // Length 1 vs length 3: degenerate "all common prefix is just the first
    // element" case.
    run_lex_test_unequal<V>(proofs, view_cfg, {{1, 3}}, {{1, 3}, {1, 3}, {1, 3}});
    run_lex_test_unequal<V>(proofs, view_cfg, {{1, 3}, {1, 3}, {1, 3}}, {{1, 3}});

    // Degenerate (issue #254): empty operands and all-fixed operands.
    // Empty-vs-empty: equal, so the non-strict variants hold and the strict
    // ones do not. Empty-vs-nonempty: the empty side is a strict prefix.
    run_lex_test_unequal<V>(proofs, view_cfg, {}, {});       // equal-length empty: depends on or_equal
    run_lex_test_unequal<V>(proofs, view_cfg, {}, {{1, 3}}); // empty < [x]
    run_lex_test_unequal<V>(proofs, view_cfg, {{1, 3}}, {}); // [x] > empty
    // All-fixed (singleton) operands, both directions.
    run_lex_test_unequal<V>(proofs, view_cfg, {{1, 1}}, {{2, 2}});                 // [1] < [2]
    run_lex_test_unequal<V>(proofs, view_cfg, {{1, 1}, {2, 2}}, {{1, 1}, {2, 2}}); // equal
    run_lex_test_unequal<V>(proofs, view_cfg, {{1, 1}, {3, 3}}, {{1, 1}, {2, 2}}); // [1,3] > [1,2]
}

// Dup-variable test: Lex with the same handle appearing across the two
// arrays. LexLess(xs, xs) is UNSAT; LexLessEqual(xs, xs) is tautology;
// {x, y} <=lex {x, z} reduces to y <= z. Consistency isn't checked on
// dup runs; see tmp/duplicate_var_audit.md.
template <LexVariant V>
auto run_dup_lex_test(bool proofs, const string & label, const vector<pair<int, int>> & unique_domains, const vector<int> & left_positions,
    const vector<int> & right_positions) -> void
{
    print(cerr, "lex dup {} {} domains={} left={} right={}{}", variant_name<V>(), label, unique_domains, left_positions, right_positions,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & vals) -> bool {
            vector<int> l, r;
            for (auto pos : left_positions)
                l.push_back(vals.at(pos));
            for (auto pos : right_positions)
                r.push_back(vals.at(pos));
            return cmp_lex<V>(l, r);
        },
        unique_domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> left, right;
    for (auto pos : left_positions)
        left.push_back(unique_vars.at(pos));
    for (auto pos : right_positions)
        right.push_back(unique_vars.at(pos));
    post_lex<V>(p, left, right);

    auto proof_name = proofs ? make_optional("lex_test_dup_" + label) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars});
    check_results(proof_name, expected, actual);
}

auto run_all_dup_tests(bool proofs) -> void
{
    // LexCompare(xs, xs) — strict UNSAT, non-strict tautology.
    // Use distinct unique vars for the two-element xs.
    run_dup_lex_test<LexVariant::LessThan>(proofs, "lt_same", {{0, 2}, {0, 2}}, {0, 1}, {0, 1});
    run_dup_lex_test<LexVariant::LessThanEqual>(proofs, "le_same", {{0, 2}, {0, 2}}, {0, 1}, {0, 1});
    run_dup_lex_test<LexVariant::GreaterThan>(proofs, "gt_same", {{0, 2}, {0, 2}}, {0, 1}, {0, 1});
    run_dup_lex_test<LexVariant::GreaterEqual>(proofs, "ge_same", {{0, 2}, {0, 2}}, {0, 1}, {0, 1});

    // {x, y} <=lex {x, z} — first positions equal → y <=lex z.
    run_dup_lex_test<LexVariant::LessThanEqual>(proofs, "le_share0", {{0, 2}, {0, 2}, {0, 2}}, {0, 1}, {0, 2});

    // {x, y} <lex {x, z} — first positions equal → y < z.
    run_dup_lex_test<LexVariant::LessThan>(proofs, "lt_share0", {{0, 2}, {0, 2}, {0, 2}}, {0, 1}, {0, 2});

    // Within-left dup: {x, x} <=lex {a, b}.
    run_dup_lex_test<LexVariant::LessThanEqual>(proofs, "le_dupleft", {{1, 3}, {1, 3}, {1, 3}}, {0, 0}, {1, 2});

    // Within-right dup: {a, b} <lex {x, x}.
    run_dup_lex_test<LexVariant::LessThan>(proofs, "lt_dupright", {{1, 3}, {1, 3}, {1, 3}}, {0, 1}, {2, 2});
}

auto run_all_tests(bool proofs, const ViewWrapConfig & view_cfg) -> void
{
    run_variant_tests<LexVariant::GreaterThan>(proofs, view_cfg);
    run_variant_tests<LexVariant::GreaterEqual>(proofs, view_cfg);
    run_variant_tests<LexVariant::LessThan>(proofs, view_cfg);
    run_variant_tests<LexVariant::LessThanEqual>(proofs, view_cfg);

    run_reified_variant_tests<LexVariant::GreaterThan, ReifKind::If>(proofs, view_cfg);
    run_reified_variant_tests<LexVariant::GreaterThan, ReifKind::Iff>(proofs, view_cfg);
    run_reified_variant_tests<LexVariant::GreaterEqual, ReifKind::If>(proofs, view_cfg);
    run_reified_variant_tests<LexVariant::GreaterEqual, ReifKind::Iff>(proofs, view_cfg);
    run_reified_variant_tests<LexVariant::LessThan, ReifKind::If>(proofs, view_cfg);
    run_reified_variant_tests<LexVariant::LessThan, ReifKind::Iff>(proofs, view_cfg);
    run_reified_variant_tests<LexVariant::LessThanEqual, ReifKind::If>(proofs, view_cfg);
    run_reified_variant_tests<LexVariant::LessThanEqual, ReifKind::Iff>(proofs, view_cfg);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Positions 0..5 cover the length-3 case fully (both 3-element arrays);
    // longer sub-tests (e.g. length-6) only get their first 6 positions
    // wrapped in single-position mode, all positions under the uniform wrap.
    constexpr int n_positions = 6;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "lex view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs, view_cfg);
        if (run_dup)
            run_all_dup_tests(proofs);
    }

    return EXIT_SUCCESS;
}
