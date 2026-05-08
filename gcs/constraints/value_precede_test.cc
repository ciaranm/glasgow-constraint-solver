#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/value_precede.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <optional>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <variant>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using std::back_inserter;
using std::cerr;
using std::flush;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::sample;
using std::set;
using std::tuple;
using std::uniform_int_distribution;
using std::variant;
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

auto run_value_precede_test(bool proofs, const vector<int> & chain, const vector<variant<int, pair<int, int>>> & domains) -> void
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
    for (const auto & entry : domains)
        vars.push_back(visit([&](auto e) { return create_integer_variable_or_constant(p, e); }, entry));
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
    run_value_precede_test(proofs, {1, 2}, {pair{1, 2}, pair{1, 2}});
    run_value_precede_test(proofs, {1, 2}, {pair{1, 2}, pair{1, 2}, pair{1, 2}});
    run_value_precede_test(proofs, {1, 2}, {pair{1, 3}, pair{1, 3}, pair{1, 3}});

    // Length-2 with values not present in any domain → trivially satisfied.
    run_value_precede_test(proofs, {5, 6}, {pair{1, 3}, pair{1, 3}, pair{1, 3}});
    run_value_precede_test(proofs, {1, 5}, {pair{1, 3}, pair{1, 3}});

    // Length-2 with t reachable only after positions that can be s.
    run_value_precede_test(proofs, {1, 2}, {pair{2, 3}, pair{1, 2}, pair{1, 2}});

    // Length-2 with the first position forced to t (unsat).
    run_value_precede_test(proofs, {1, 2}, {pair{2, 2}, pair{1, 2}});

    // Length-3 chain — value_precede_chain.
    run_value_precede_test(proofs, {1, 2, 3}, {pair{1, 3}, pair{1, 3}, pair{1, 3}});
    run_value_precede_test(proofs, {1, 2, 3}, {pair{1, 3}, pair{1, 3}, pair{1, 3}, pair{1, 3}});

    // Chain values out of order in domains.
    run_value_precede_test(proofs, {3, 1, 2}, {pair{1, 3}, pair{1, 3}, pair{1, 3}});

    // Length-4 chain.
    run_value_precede_test(proofs, {1, 2, 3, 4}, {pair{1, 4}, pair{1, 4}, pair{1, 4}, pair{1, 4}});

    // Repeated chain values: {1, 2, 1} requires 1≺2 AND 2≺1, only satisfiable
    // when no 1 or 2 appears.
    run_value_precede_test(proofs, {1, 2, 1}, {pair{1, 3}, pair{1, 3}, pair{1, 3}});

    // Repeated adjacent values: {1, 1} is a no-op pair.
    run_value_precede_test(proofs, {1, 1}, {pair{1, 2}, pair{1, 2}, pair{1, 2}});

    // Empty chain and length-1 chain — trivially satisfied (no propagator).
    run_value_precede_test(proofs, {}, {pair{1, 2}, pair{1, 2}});
    run_value_precede_test(proofs, {7}, {pair{1, 2}, pair{1, 2}});

    // Negative values.
    run_value_precede_test(proofs, {-1, 1}, {pair{-1, 1}, pair{-1, 1}, pair{-1, 1}});

    // Constant entries: a position pinned to a chain value.
    run_value_precede_test(proofs, {1, 2}, {1, pair{1, 3}, pair{1, 3}});
    run_value_precede_test(proofs, {1, 2}, {pair{1, 3}, 2, pair{1, 3}});  // unsat: forces 2 in pos 1 with no preceding 1
    run_value_precede_test(proofs, {1, 2, 3}, {1, pair{1, 3}, 2, pair{1, 3}});
}

auto main(int, char *[]) -> int
{
    random_device rand_dev;
    mt19937 rand(rand_dev());

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs);

        // Random sweep: chain length 1..3 of distinct values from {1..4},
        // domains length 2..5 over {1..4}. With domain 4 and length 5 the
        // unconstrained space is 4^5 = 1024 — VeriPB stays well under
        // a second per case, and value_precede is selective in practice.
        uniform_int_distribution chain_len_dist{1, 3};
        uniform_int_distribution n_vars_dist{2, 5};
        for (int x = 0; x < 8; ++x) {
            int chain_len = chain_len_dist(rand);
            vector<int> chain_pool{1, 2, 3, 4};
            vector<int> chain;
            sample(chain_pool.begin(), chain_pool.end(), back_inserter(chain), chain_len, rand);
            int n_vars = n_vars_dist(rand);
            vector<variant<int, pair<int, int>>> doms;
            for (int i = 0; i < n_vars; ++i)
                doms.emplace_back(generate_random_data_item(rand, random_bounds_or_constant(1, 2, 1, 2)));
            run_value_precede_test(proofs, chain, doms);
        }
    }

    return EXIT_SUCCESS;
}
