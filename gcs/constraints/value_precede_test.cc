#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/value_precede.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
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

namespace
{
    auto satisfies_value_precede(const vector<int> & chain, const vector<int> & vs) -> bool
    {
        for (size_t j = 1; j < chain.size(); ++j) {
            int s = chain[j - 1], t = chain[j];
            for (size_t i = 0; i < vs.size(); ++i) {
                if (vs[i] == t) {
                    bool found_s = false;
                    for (size_t k = 0; k < i; ++k)
                        if (vs[k] == s) {
                            found_s = true;
                            break;
                        }
                    if (! found_s)
                        return false;
                }
            }
        }
        return true;
    }
}

auto run_value_precede_test(bool proofs, const vector<int> & chain, const vector<pair<int, int>> & domains) -> void
{
    print(cerr, "value_precede chain={} domains={}{}",
        chain, domains, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [chain](const vector<int> & vs) {
        return satisfies_value_precede(chain, vs);
    }, domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & d : domains)
        vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<Integer> chain_i;
    for (const auto & v : chain)
        chain_i.push_back(Integer(v));
    p.post(ValuePrecede{chain_i, vars});

    auto proof_name = proofs ? make_optional("value_precede_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs) -> void
{
    // Length-2 chain — basic value_precede.
    run_value_precede_test(proofs, {1, 2}, {{1, 2}, {1, 2}});
    run_value_precede_test(proofs, {1, 2}, {{1, 2}, {1, 2}, {1, 2}});
    run_value_precede_test(proofs, {1, 2}, {{1, 3}, {1, 3}, {1, 3}});

    // Length-2 with values not present in any domain → trivially satisfied.
    run_value_precede_test(proofs, {5, 6}, {{1, 3}, {1, 3}, {1, 3}});
    run_value_precede_test(proofs, {1, 5}, {{1, 3}, {1, 3}});

    // Length-2 with t reachable only after positions that can be s.
    run_value_precede_test(proofs, {1, 2}, {{2, 3}, {1, 2}, {1, 2}});

    // Length-2 with the first position forced to t (unsat).
    run_value_precede_test(proofs, {1, 2}, {{2, 2}, {1, 2}});

    // Length-3 chain — value_precede_chain.
    run_value_precede_test(proofs, {1, 2, 3}, {{1, 3}, {1, 3}, {1, 3}});
    run_value_precede_test(proofs, {1, 2, 3}, {{1, 3}, {1, 3}, {1, 3}, {1, 3}});

    // Chain values out of order in domains.
    run_value_precede_test(proofs, {3, 1, 2}, {{1, 3}, {1, 3}, {1, 3}});

    // Length-4 chain.
    run_value_precede_test(proofs, {1, 2, 3, 4}, {{1, 4}, {1, 4}, {1, 4}, {1, 4}});

    // Repeated chain values: {1, 2, 1} requires 1≺2 AND 2≺1, only satisfiable
    // when no 1 or 2 appears.
    run_value_precede_test(proofs, {1, 2, 1}, {{1, 3}, {1, 3}, {1, 3}});

    // Repeated adjacent values: {1, 1} is a no-op pair.
    run_value_precede_test(proofs, {1, 1}, {{1, 2}, {1, 2}, {1, 2}});

    // Empty chain and length-1 chain — trivially satisfied (no propagator).
    run_value_precede_test(proofs, {}, {{1, 2}, {1, 2}});
    run_value_precede_test(proofs, {7}, {{1, 2}, {1, 2}});

    // Negative values.
    run_value_precede_test(proofs, {-1, 1}, {{-1, 1}, {-1, 1}, {-1, 1}});
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
