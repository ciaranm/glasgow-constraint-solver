#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/regular.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
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
using std::ranges::find;
using std::set;
using std::string;
using std::tuple;
using std::unordered_map;
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

// Build a complete transition table initialised to -1 (no transition) everywhere,
// then apply the given edges. The propagator uses operator[] which returns 0 for
// absent keys — NOT -1 — so every reachable (state, symbol) pair must be explicit.
auto make_transitions(int num_states, int num_symbols, vector<tuple<int, int, int>> edges)
    -> vector<unordered_map<Integer, long>>
{
    vector<unordered_map<Integer, long>> trans(num_states);
    for (int q = 0; q < num_states; ++q)
        for (int j = 0; j < num_symbols; ++j)
            trans[q][Integer(j)] = -1L;
    for (auto [from, sym, to] : edges)
        trans[from][Integer(sym)] = to;
    return trans;
}

// symbols must be {0_i, 1_i, ..., n-1_i} — see Regular's documentation.
auto run_regular_test(bool proofs, const string & desc,
    vector<pair<int, int>> var_ranges,
    vector<Integer> symbols,
    long num_states,
    vector<unordered_map<Integer, long>> transitions,
    vector<long> final_states) -> void
{
    print(cerr, "regular {} {} vars{}", desc, var_ranges.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    auto dfa_accepts = [&](const vector<int> & seq) -> bool {
        long state = 0;
        for (int val : seq) {
            auto it = transitions[state].find(Integer(val));
            if (it == transitions[state].end() || it->second == -1L)
                return false;
            state = it->second;
        }
        return find(final_states, state) != final_states.end();
    };

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [&](vector<int> seq) { return dfa_accepts(seq); }, var_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & [lo, hi] : var_ranges)
        vars.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));
    p.post(Regular{vars, symbols, num_states, transitions, final_states});

    auto proof_name = proofs ? make_optional("regular_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs) -> void
{
    // DFA: even number of 0s, binary alphabet {0,1}
    // State 0 (initial, final): 0->1, 1->0
    // State 1: 0->0, 1->1
    run_regular_test(proofs, "even zeros",
        {{0, 1}, {0, 1}, {0, 1}},
        {0_i, 1_i}, 2,
        make_transitions(2, 2, {{0, 0, 1}, {0, 1, 0}, {1, 0, 0}, {1, 1, 1}}),
        {0});

    // DFA: no two consecutive 0s, binary alphabet {0,1}
    // State 0 (initial, final): 0->1, 1->0
    // State 1 (final, last was 0): 0->dead(-1), 1->0
    run_regular_test(proofs, "no consecutive 0s",
        {{0, 1}, {0, 1}, {0, 1}, {0, 1}},
        {0_i, 1_i}, 2,
        make_transitions(2, 2, {{0, 0, 1}, {0, 1, 0}, {1, 1, 0}}),
        {0, 1});

    // DFA: sequence contains at least one 2, ternary alphabet {0,1,2}
    // State 0: 0->0, 1->0, 2->1
    // State 1 (final): all symbols -> 1
    run_regular_test(proofs, "contains 2",
        {{0, 2}, {0, 2}, {0, 2}},
        {0_i, 1_i, 2_i}, 2,
        make_transitions(2, 3, {{0, 0, 0}, {0, 1, 0}, {0, 2, 1}, {1, 0, 1}, {1, 1, 1}, {1, 2, 1}}),
        {1});

    // Same DFA: first two variables restricted to {0,1}, last to {0,1,2}.
    // GAC must prune the last variable's domain to {2} at the root, since
    // no accepting path exists unless some variable carries the value 2.
    run_regular_test(proofs, "contains 2, last forced to 2",
        {{0, 1}, {0, 1}, {0, 2}},
        {0_i, 1_i, 2_i}, 2,
        make_transitions(2, 3, {{0, 0, 0}, {0, 1, 0}, {0, 2, 1}, {1, 0, 1}, {1, 1, 1}, {1, 2, 1}}),
        {1});

    // DFA: all symbols in the sequence must be identical, binary alphabet {0,1}
    // State 0 (initial): 0->1, 1->2
    // State 1 (all 0s so far, final): 0->1, 1->3(dead)
    // State 2 (all 1s so far, final): 0->3(dead), 1->2
    // State 3 (dead): 0->3, 1->3
    run_regular_test(proofs, "all same",
        {{0, 1}, {0, 1}, {0, 1}, {0, 1}},
        {0_i, 1_i}, 4,
        make_transitions(4, 2, {{0, 0, 1}, {0, 1, 2}, {1, 0, 1}, {1, 1, 3}, {2, 0, 3}, {2, 1, 2}, {3, 0, 3}, {3, 1, 3}}),
        {1, 2});

    // Unsatisfiable: no final states
    run_regular_test(proofs, "no final states",
        {{0, 1}, {0, 1}, {0, 1}},
        {0_i, 1_i}, 2,
        make_transitions(2, 2, {{0, 0, 1}, {0, 1, 0}, {1, 0, 0}, {1, 1, 1}}),
        {});

    // Unsatisfiable: variable domains exclude all accepting paths.
    // "Contains 2" DFA with all variables restricted to {0,1} — 2 is never reachable.
    run_regular_test(proofs, "domain excludes accepting paths",
        {{0, 1}, {0, 1}, {0, 1}},
        {0_i, 1_i, 2_i}, 2,
        make_transitions(2, 3, {{0, 0, 0}, {0, 1, 0}, {0, 2, 1}, {1, 0, 1}, {1, 1, 1}, {1, 2, 1}}),
        {1});
}

auto main(int, char *[]) -> int
{
    run_all_tests(false);

    if (can_run_veripb())
        run_all_tests(true);

    return EXIT_SUCCESS;
}
