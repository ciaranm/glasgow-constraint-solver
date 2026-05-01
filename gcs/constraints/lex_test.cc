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

auto run_lex_test_2(bool proofs,
    pair<int, int> r1, pair<int, int> r2,
    pair<int, int> r3, pair<int, int> r4) -> void
{
    print(cerr, "lex 2 [{},{}] [{},{}] > [{},{}] [{},{}]{}",
        r1.first, r1.second, r2.first, r2.second,
        r3.first, r3.second, r4.first, r4.second,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int>> expected, actual;
    build_expected(expected, [](int a1, int a2, int b1, int b2) {
        return tie(a1, a2) > tie(b1, b2);
    }, r1, r2, r3, r4);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    auto v3 = p.create_integer_variable(Integer(r3.first), Integer(r3.second));
    auto v4 = p.create_integer_variable(Integer(r4.first), Integer(r4.second));
    p.post(Lex{{v1, v2}, {v3, v4}});

    auto proof_name = proofs ? make_optional("lex_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, v4});
    check_results(proof_name, expected, actual);
}

auto run_lex_test_3(bool proofs,
    pair<int, int> r1, pair<int, int> r2, pair<int, int> r3,
    pair<int, int> r4, pair<int, int> r5, pair<int, int> r6) -> void
{
    print(cerr, "lex 3 [{},{}] [{},{}] [{},{}] > [{},{}] [{},{}] [{},{}]{}",
        r1.first, r1.second, r2.first, r2.second, r3.first, r3.second,
        r4.first, r4.second, r5.first, r5.second, r6.first, r6.second,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int, int, int>> expected, actual;
    build_expected(expected, [](int a1, int a2, int a3, int b1, int b2, int b3) {
        return tie(a1, a2, a3) > tie(b1, b2, b3);
    }, r1, r2, r3, r4, r5, r6);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    auto v3 = p.create_integer_variable(Integer(r3.first), Integer(r3.second));
    auto v4 = p.create_integer_variable(Integer(r4.first), Integer(r4.second));
    auto v5 = p.create_integer_variable(Integer(r5.first), Integer(r5.second));
    auto v6 = p.create_integer_variable(Integer(r6.first), Integer(r6.second));
    p.post(Lex{{v1, v2, v3}, {v4, v5, v6}});

    auto proof_name = proofs ? make_optional("lex_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, v4, v5, v6});
    check_results(proof_name, expected, actual);
}

auto run_lex_test_6(bool proofs,
    pair<int, int> r1, pair<int, int> r2, pair<int, int> r3,
    pair<int, int> r4, pair<int, int> r5, pair<int, int> r6,
    pair<int, int> r7, pair<int, int> r8, pair<int, int> r9,
    pair<int, int> r10, pair<int, int> r11, pair<int, int> r12) -> void
{
    print(cerr, "lex 6 with proofs={}:", proofs);
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [](vector<int> v) {
        return tie(v[0], v[1], v[2], v[3], v[4], v[5]) > tie(v[6], v[7], v[8], v[9], v[10], v[11]);
    }, vector<pair<int, int>>{r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> all_vars;
    for (const auto & r : {r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12})
        all_vars.push_back(p.create_integer_variable(Integer(r.first), Integer(r.second)));

    p.post(Lex{vector<IntegerVariableID>{all_vars.begin(), all_vars.begin() + 6},
        vector<IntegerVariableID>{all_vars.begin() + 6, all_vars.end()}});

    auto proof_name = proofs ? make_optional("lex_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{all_vars});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs) -> void
{
    // Length-2: same domain for both arrays
    run_lex_test_2(proofs, {1, 3}, {1, 3}, {1, 3}, {1, 3});
    run_lex_test_2(proofs, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Length-2: asymmetric domains — first position dominates
    run_lex_test_2(proofs, {2, 4}, {1, 3}, {1, 3}, {1, 3});

    // Length-2: first positions equal, second position determines order
    run_lex_test_2(proofs, {1, 2}, {1, 3}, {1, 2}, {1, 3});

    // Length-2: unsatisfiable — vars_2 strictly dominates vars_1
    run_lex_test_2(proofs, {1, 1}, {1, 2}, {2, 3}, {3, 4});

    // Length-2: negative values
    run_lex_test_2(proofs, {-2, 1}, {-2, 1}, {-2, 1}, {-2, 1});

    // Length-2: larger domain
    run_lex_test_2(proofs, {1, 6}, {1, 6}, {1, 6}, {1, 6});

    // Length-3: same domain for both arrays
    run_lex_test_3(proofs, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {1, 3});
    run_lex_test_3(proofs, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2});

    // Length-3: asymmetric domains
    run_lex_test_3(proofs, {1, 3}, {1, 2}, {1, 3}, {1, 2}, {1, 3}, {1, 2});

    // Length-3: first two positions equal, third determines order
    run_lex_test_3(proofs, {1, 2}, {1, 2}, {1, 3}, {1, 2}, {1, 2}, {1, 3});

    // Length-3 GAC: middle position forces witness at position 0.
    // vars_1[1] = 1 < vars_2[1] = 2 prefix-blocks any witness at position >= 1,
    // so the only witness can be position 0, forcing vars_1[0] > vars_2[0].
    run_lex_test_3(proofs, {1, 2}, {1, 1}, {1, 2}, {1, 2}, {2, 2}, {1, 2});

    // Length-3: larger domain
    run_lex_test_3(proofs, {1, 5}, {1, 5}, {1, 5}, {1, 5}, {1, 5}, {1, 5});

    // Length-6 with small domains, to exercise longer chains
    run_lex_test_6(proofs,
        {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2},
        {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2}, {1, 2});
}

auto main(int, char *[]) -> int
{
    run_all_tests(false);

    if (can_run_veripb())
        run_all_tests(true);

    return EXIT_SUCCESS;
}
