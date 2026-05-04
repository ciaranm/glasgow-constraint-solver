#include <gcs/constraints/at_most_one.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
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

auto run_at_most_one_test_3(bool proofs,
    pair<int, int> r1, pair<int, int> r2, pair<int, int> r3,
    pair<int, int> r_val) -> void
{
    print(cerr, "at_most_one 3 {} {} {} val={}{}", r1, r2, r3, r_val, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int>> expected, actual;
    build_expected(expected, [](int a, int b, int c, int v) {
        return (a == v) + (b == v) + (c == v) <= 1;
    }, r1, r2, r3, r_val);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    auto v3 = p.create_integer_variable(Integer(r3.first), Integer(r3.second));
    auto val = p.create_integer_variable(Integer(r_val.first), Integer(r_val.second));
    p.post(AtMostOne{{v1, v2, v3}, val});

    auto proof_name = proofs ? make_optional("at_most_one_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, val});
    check_results(proof_name, expected, actual);
}

auto run_at_most_one_test_4(bool proofs,
    pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, pair<int, int> r4,
    pair<int, int> r_val) -> void
{
    print(cerr, "at_most_one 4 {} {} {} {} val={}{}", r1, r2, r3, r4, r_val, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, int, int>> expected, actual;
    build_expected(expected, [](int a, int b, int c, int d, int v) {
        return (a == v) + (b == v) + (c == v) + (d == v) <= 1;
    }, r1, r2, r3, r4, r_val);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    auto v3 = p.create_integer_variable(Integer(r3.first), Integer(r3.second));
    auto v4 = p.create_integer_variable(Integer(r4.first), Integer(r4.second));
    auto val = p.create_integer_variable(Integer(r_val.first), Integer(r_val.second));
    p.post(AtMostOne{{v1, v2, v3, v4}, val});

    auto proof_name = proofs ? make_optional("at_most_one_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, v4, val});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs) -> void
{
    // 3-variable tests, fixed val (single-point range)
    run_at_most_one_test_3(proofs, {1, 3}, {1, 3}, {1, 3}, {2, 2});          // basic, val=2
    run_at_most_one_test_3(proofs, {1, 3}, {1, 3}, {1, 3}, {5, 5});          // val outside all domains: all trivially satisfy
    run_at_most_one_test_3(proofs, {1, 3}, {1, 3}, {1, 3}, {1, 1});          // val at domain boundary
    run_at_most_one_test_3(proofs, {-2, 2}, {-2, 2}, {-2, 2}, {0, 0});       // negative domain, val=0

    // 3-variable tests, variable val: val itself can change
    run_at_most_one_test_3(proofs, {1, 3}, {1, 3}, {1, 3}, {1, 3});          // val same range as vars
    run_at_most_one_test_3(proofs, {1, 3}, {1, 3}, {1, 3}, {2, 4});          // val range overlaps vars

    // Propagation: one var forced to equal val, so all others must differ
    run_at_most_one_test_3(proofs, {2, 2}, {1, 3}, {1, 3}, {2, 2});          // v1 forced to val=2, v2/v3 must != 2
    run_at_most_one_test_3(proofs, {2, 2}, {2, 2}, {1, 3}, {1, 3});          // v1=v2=2, val must move away from 2

    // Unsatisfiable: two vars forced to equal a fixed val
    run_at_most_one_test_3(proofs, {2, 2}, {2, 2}, {1, 3}, {2, 2});

    // 4-variable tests, fixed val
    run_at_most_one_test_4(proofs, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {2, 2});
    run_at_most_one_test_4(proofs, {2, 2}, {1, 3}, {1, 3}, {1, 3}, {2, 2});  // propagation with 4 vars

    // 4-variable tests, variable val
    run_at_most_one_test_4(proofs, {1, 3}, {1, 3}, {1, 3}, {1, 3}, {1, 3});
    run_at_most_one_test_4(proofs, {2, 2}, {2, 2}, {1, 3}, {1, 3}, {1, 3}); // v1=v2=2, val can't be 2
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
