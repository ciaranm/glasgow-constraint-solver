#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/seq_precede_chain.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <chrono>
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
using std::chrono::duration;
using std::chrono::steady_clock;

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
    auto satisfies_seq_precede_chain(const vector<int> & vs) -> bool
    {
        for (size_t i = 0; i < vs.size(); ++i) {
            if (vs[i] >= 2) {
                bool found = false;
                for (size_t k = 0; k < i; ++k)
                    if (vs[k] == vs[i] - 1) {
                        found = true;
                        break;
                    }
                if (! found)
                    return false;
            }
        }
        return true;
    }
}

auto run_test(bool proofs, const vector<pair<int, int>> & domains) -> void
{
    print(cerr, "seq_precede_chain domains={}{}",
        domains, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [](const vector<int> & vs) {
        return satisfies_seq_precede_chain(vs);
    }, domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & d : domains)
        vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    p.post(SeqPrecedeChain{vars});

    auto proof_name = proofs ? make_optional("seq_precede_chain_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

auto run_scale_test(bool proofs) -> void
{
    print(cerr, "seq_precede_chain scale (length 5, domain 1..1000){}",
        proofs ? " with proofs:" : ":");
    cerr << flush;

    auto start = steady_clock::now();

    Problem p;
    vector<IntegerVariableID> vars;
    for (int i = 0; i < 5; ++i)
        vars.push_back(p.create_integer_variable(1_i, 1000_i));
    p.post(SeqPrecedeChain{vars});

    set<tuple<vector<int>>> actual;
    auto proof_name = proofs ? make_optional("seq_precede_chain_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{vars});

    auto solve_elapsed = duration<double>(steady_clock::now() - start).count();
    println(cerr, " got {} solutions in {:.2f}s", actual.size(), solve_elapsed);

    if (actual.size() != 52)
        throw UnexpectedException{"scale test expected 52 solutions (Bell number B(5))"};

    if (proofs) {
        auto verify_start = steady_clock::now();
        if (! run_veripb("seq_precede_chain_test.opb", "seq_precede_chain_test.pbp"))
            throw UnexpectedException{"veripb verification failed on scale test"};
        auto verify_elapsed = duration<double>(steady_clock::now() - verify_start).count();
        println(cerr, "  veripb verification: {:.2f}s", verify_elapsed);
    }
}

auto run_all_tests(bool proofs) -> void
{
    // Length-2: smallest meaningful chain.
    run_test(proofs, {{1, 2}, {1, 2}});
    run_test(proofs, {{1, 5}, {1, 5}});

    // Length-3 with domain == array length, no truncation needed.
    run_test(proofs, {{1, 3}, {1, 3}, {1, 3}});

    // Length-3 with domain > array length, exercises truncation.
    run_test(proofs, {{1, 6}, {1, 6}, {1, 6}});

    // Length-5 with domain 2x array length: the headline case scaled
    // down enough for build_expected.
    run_test(proofs, {{1, 10}, {1, 10}, {1, 10}, {1, 10}, {1, 10}});

    // Negative and zero values: unconstrained by the chain.
    run_test(proofs, {{-2, 3}, {-2, 3}, {-2, 3}});

    // Non-uniform domains, one var with a wildly larger upper bound.
    // Catches any "compute max from initial_state" bug.
    run_test(proofs, {{1, 4}, {1, 4}, {1, 100}, {1, 4}});

    // Empty array: trivially satisfied.
    run_test(proofs, {});
}

auto main(int, char *[]) -> int
{
    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs);
        run_scale_test(proofs);
    }

    return EXIT_SUCCESS;
}
