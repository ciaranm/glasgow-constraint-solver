#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/table/negative_table.hh>
#include <gcs/extensional.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <util/overloaded.hh>

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

auto run_negative_table_test_2(bool proofs, pair<int, int> r1, pair<int, int> r2, SimpleTuples forbidden) -> void
{
    print(cerr, "negative table 2var [{},{}] [{},{}] {} tuples{}",
        r1.first, r1.second, r2.first, r2.second, forbidden.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int>> expected, actual;
    build_expected(expected, [&](int a, int b) -> bool {
        for (const auto & t : forbidden)
            if (t[0].raw_value == a && t[1].raw_value == b)
                return false;
        return true; }, r1, r2);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    p.post(NegativeTable{{v1, v2}, forbidden});

    auto proof_name = proofs ? make_optional("negative_table_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v1, v2});
    check_results(proof_name, expected, actual);
}

auto run_negative_table_test_3(bool proofs, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, SimpleTuples forbidden) -> void
{
    print(cerr, "negative table 3var [{},{}] [{},{}] [{},{}] {} tuples{}",
        r1.first, r1.second, r2.first, r2.second, r3.first, r3.second, forbidden.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, [&](int a, int b, int c) -> bool {
        for (const auto & t : forbidden)
            if (t[0].raw_value == a && t[1].raw_value == b && t[2].raw_value == c)
                return false;
        return true; }, r1, r2, r3);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    auto v3 = p.create_integer_variable(Integer(r3.first), Integer(r3.second));
    p.post(NegativeTable{{v1, v2, v3}, forbidden});

    auto proof_name = proofs ? make_optional("negative_table_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});
    check_results(proof_name, expected, actual);
}

auto run_negative_wildcard_table_test(bool proofs, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, WildcardTuples forbidden) -> void
{
    print(cerr, "negative wildcard table [{},{}] [{},{}] [{},{}] {} tuples{}",
        r1.first, r1.second, r2.first, r2.second, r3.first, r3.second, forbidden.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    auto entry_matches = [](const IntegerOrWildcard & entry, int val) -> bool {
        return overloaded{
            [val](Integer i) { return i.raw_value == val; },
            [](Wildcard) { return true; }}
            .visit(entry);
    };

    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, [&](int a, int b, int c) -> bool {
        for (const auto & t : forbidden)
            if (entry_matches(t[0], a) && entry_matches(t[1], b) && entry_matches(t[2], c))
                return false;
        return true; }, r1, r2, r3);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(r1.first), Integer(r1.second));
    auto v2 = p.create_integer_variable(Integer(r2.first), Integer(r2.second));
    auto v3 = p.create_integer_variable(Integer(r3.first), Integer(r3.second));
    p.post(NegativeTable{{v1, v2, v3}, forbidden});

    auto proof_name = proofs ? make_optional("negative_table_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs) -> void
{
    // Two-variable cases.
    run_negative_table_test_2(proofs, {1, 3}, {1, 3},
        {{1_i, 1_i}}); // single forbidden
    run_negative_table_test_2(proofs, {1, 3}, {1, 3},
        {{1_i, 1_i}, {2_i, 2_i}, {3_i, 3_i}}); // exclude diagonal
    run_negative_table_test_2(proofs, {1, 2}, {1, 2},
        {{1_i, 1_i}, {1_i, 2_i}, {2_i, 1_i}, {2_i, 2_i}}); // all forbidden: unsat at root
    run_negative_table_test_2(proofs, {1, 3}, {2, 2},
        {{1_i, 2_i}}); // singleton domain forces v1!=1 at root (unit at init)
    run_negative_table_test_2(proofs, {1, 3}, {1, 3},
        {{4_i, 4_i}, {1_i, 1_i}}); // first tuple already infeasible (4 not in dom): satisfied automatically
    run_negative_table_test_2(proofs, {1, 3}, {1, 3},
        {{1_i, 1_i}, {1_i, 1_i}, {2_i, 2_i}}); // duplicates in forbidden list

    // Three-variable cases.
    run_negative_table_test_3(proofs, {1, 3}, {1, 3}, {1, 3},
        {{1_i, 1_i, 1_i}, {2_i, 2_i, 2_i}, {3_i, 3_i, 3_i}}); // exclude diagonal
    run_negative_table_test_3(proofs, {1, 2}, {1, 2}, {1, 2},
        {{1_i, 1_i, 1_i}, {1_i, 1_i, 2_i}, {1_i, 2_i, 1_i}, {1_i, 2_i, 2_i},
            {2_i, 1_i, 1_i}, {2_i, 1_i, 2_i}, {2_i, 2_i, 1_i}, {2_i, 2_i, 2_i}}); // all forbidden: unsat
    run_negative_table_test_3(proofs, {1, 3}, {2, 4}, {1, 2},
        {{1_i, 2_i, 1_i}, {3_i, 4_i, 2_i}});
    run_negative_table_test_3(proofs, {1, 3}, {1, 3}, {1, 3},
        {{1_i, 1_i, 1_i}, {1_i, 1_i, 2_i}, {1_i, 1_i, 3_i}}); // (1,1,*) all forbidden: forces v1!=1 OR v2!=1 (cascade)
    run_negative_table_test_3(proofs, {-2, 2}, {-2, 2}, {-2, 2},
        {{-2_i, 0_i, 2_i}, {0_i, 0_i, 0_i}, {2_i, 0_i, -2_i}});

    // Larger forbidden tables to exercise watched-literal scaling.
    run_negative_table_test_3(proofs, {1, 4}, {1, 4}, {1, 4},
        {{1_i, 1_i, 1_i}, {1_i, 2_i, 3_i}, {2_i, 1_i, 4_i}, {2_i, 3_i, 2_i},
            {3_i, 4_i, 1_i}, {4_i, 2_i, 3_i}, {4_i, 4_i, 4_i}, {1_i, 3_i, 2_i},
            {2_i, 2_i, 2_i}, {3_i, 3_i, 3_i}});

    // Wildcard cases.
    run_negative_wildcard_table_test(proofs, {1, 3}, {1, 3}, {1, 3},
        {{{Wildcard{}, 2_i, Wildcard{}}}}); // forbid all tuples with v2=2
    run_negative_wildcard_table_test(proofs, {1, 3}, {1, 3}, {1, 3},
        {{{1_i, Wildcard{}, 3_i}, {2_i, 2_i, Wildcard{}}}}); // mixed wildcard forbids
    run_negative_wildcard_table_test(proofs, {1, 3}, {1, 3}, {1, 3},
        {{{Wildcard{}, Wildcard{}, Wildcard{}}}}); // all-wildcard tuple: unsat at root
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
