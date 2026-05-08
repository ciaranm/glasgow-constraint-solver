#include <gcs/constraints/at_most_one.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
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
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::tuple;
using std::uniform_int_distribution;
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

auto run_at_most_one_test(bool proofs,
    const vector<pair<int, int>> & ranges, pair<int, int> val_range) -> void
{
    print(cerr, "at_most_one {} val={}{}", ranges, val_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, int>> expected, actual;
    build_expected(expected,
        [](const vector<int> & vs, int v) {
            int matches = 0;
            for (auto x : vs)
                matches += (x == v);
            return matches <= 1;
        },
        ranges, val_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & [l, u] : ranges)
        vars.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    auto val = p.create_integer_variable(Integer(val_range.first), Integer(val_range.second));
    p.post(AtMostOne{vars, val});

    auto proof_name = proofs ? make_optional("at_most_one_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars, val});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs) -> void
{
    // Boundary: empty / singleton — both vacuously true.
    run_at_most_one_test(proofs, {}, {1, 3});
    run_at_most_one_test(proofs, {{1, 3}}, {1, 3});

    // Two vars: smallest meaningful case.
    run_at_most_one_test(proofs, {{1, 3}, {1, 3}}, {2, 2});
    run_at_most_one_test(proofs, {{1, 3}, {1, 3}}, {1, 3});

    // 3-variable tests, fixed val (single-point range)
    run_at_most_one_test(proofs, {{1, 3}, {1, 3}, {1, 3}}, {2, 2});          // basic, val=2
    run_at_most_one_test(proofs, {{1, 3}, {1, 3}, {1, 3}}, {5, 5});          // val outside all domains
    run_at_most_one_test(proofs, {{1, 3}, {1, 3}, {1, 3}}, {1, 1});          // val at domain boundary
    run_at_most_one_test(proofs, {{-2, 2}, {-2, 2}, {-2, 2}}, {0, 0});       // negative domain, val=0

    // 3-variable tests, variable val
    run_at_most_one_test(proofs, {{1, 3}, {1, 3}, {1, 3}}, {1, 3});
    run_at_most_one_test(proofs, {{1, 3}, {1, 3}, {1, 3}}, {2, 4});

    // Propagation: one var forced to equal val, others must differ
    run_at_most_one_test(proofs, {{2, 2}, {1, 3}, {1, 3}}, {2, 2});
    run_at_most_one_test(proofs, {{2, 2}, {2, 2}, {1, 3}}, {1, 3});

    // Unsatisfiable: two vars forced to equal a fixed val
    run_at_most_one_test(proofs, {{2, 2}, {2, 2}, {1, 3}}, {2, 2});

    // 4-variable tests
    run_at_most_one_test(proofs, {{1, 3}, {1, 3}, {1, 3}, {1, 3}}, {2, 2});
    run_at_most_one_test(proofs, {{2, 2}, {1, 3}, {1, 3}, {1, 3}}, {2, 2});
    run_at_most_one_test(proofs, {{1, 3}, {1, 3}, {1, 3}, {1, 3}}, {1, 3});
    run_at_most_one_test(proofs, {{2, 2}, {2, 2}, {1, 3}, {1, 3}}, {1, 3});
}

auto main(int, char *[]) -> int
{
    random_device rand_dev;
    mt19937 rand(rand_dev());

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs);

        // Small random sweep: 2..5 vars, modest domains so the solution
        // space stays small. Solution count is O(|val| * prod(|vars|))
        // worst case, which on these bounds is at most ~5^5 = 3125 even
        // before the at-most-one filter, so VeriPB stays fast.
        uniform_int_distribution n_vars_dist{2, 5};
        uniform_int_distribution lo_dist{-2, 4};
        uniform_int_distribution width_dist{0, 4};
        for (int x = 0; x < 10; ++x) {
            int n_vars = n_vars_dist(rand);
            vector<pair<int, int>> ranges;
            for (int i = 0; i < n_vars; ++i) {
                int lo = lo_dist(rand);
                ranges.emplace_back(lo, lo + width_dist(rand));
            }
            int v_lo = lo_dist(rand);
            run_at_most_one_test(proofs, ranges, {v_lo, v_lo + width_dist(rand)});
        }
    }

    return EXIT_SUCCESS;
}
