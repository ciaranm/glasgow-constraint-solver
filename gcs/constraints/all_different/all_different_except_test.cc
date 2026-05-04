#include <gcs/constraints/all_different/all_different_except.hh>
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
#include <fmt/ranges.h>
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

auto run_alldiffexcept_test(bool proofs, const vector<pair<int, int>> & domains, const vector<int> & excluded) -> void
{
    print(cerr, "all_different_except {} excl {}{}", domains, excluded, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [&](vector<int> v) {
        for (size_t i = 0; i < v.size(); ++i) {
            for (size_t j = i + 1; j < v.size(); ++j) {
                bool i_excl = std::find(excluded.begin(), excluded.end(), v[i]) != excluded.end();
                bool j_excl = std::find(excluded.begin(), excluded.end(), v[j]) != excluded.end();
                if (! i_excl && ! j_excl && v[i] == v[j])
                    return false;
            }
        }
        return true;
    };

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & d : domains)
        vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<Integer> excluded_i;
    for (const auto & v : excluded)
        excluded_i.push_back(Integer(v));
    p.post(AllDifferentExcept{vars, excluded_i});

    auto proof_name = proofs ? make_optional("all_different_except_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs) -> void
{
    // Empty / single — trivial cases.
    run_alldiffexcept_test(proofs, {}, {0});
    run_alldiffexcept_test(proofs, {{0, 3}}, {0});

    // Standard cases on small domains.
    run_alldiffexcept_test(proofs, {{0, 3}, {0, 3}}, {0});
    run_alldiffexcept_test(proofs, {{0, 3}, {0, 3}, {0, 3}}, {0});

    // Forces infeasibility via fixed non-excluded duplicates.
    // (Constants 1, 1 with 0 excluded: 1 != 0 so the constraint must enforce 1 != 1.)
    run_alldiffexcept_test(proofs, {{1, 1}, {1, 1}}, {0});

    // Multiple excluded values.
    run_alldiffexcept_test(proofs, {{0, 4}, {0, 4}, {0, 4}}, {0, 1});

    // No excluded values reachable: should match plain AllDifferent.
    run_alldiffexcept_test(proofs, {{1, 3}, {1, 3}, {1, 3}}, {7});

    // All values reachable are excluded: constraint trivially satisfied.
    run_alldiffexcept_test(proofs, {{0, 1}, {0, 1}, {0, 1}}, {0, 1});

    // Mix where pruning by Hall set is exercised.
    run_alldiffexcept_test(proofs, {{0, 2}, {1, 2}, {1, 2}}, {0});
    run_alldiffexcept_test(proofs, {{0, 1}, {0, 1}, {0, 2}, {0, 2}}, {0});
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
