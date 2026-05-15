#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/mdd.hh>
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

auto run_mdd_test(bool proofs, const string & desc,
    vector<pair<int, int>> var_ranges,
    vector<vector<unordered_map<Integer, long>>> layer_transitions,
    vector<long> nodes_per_layer,
    vector<long> accepting_terminals) -> void
{
    print(cerr, "mdd {} {} vars{}", desc, var_ranges.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    auto mdd_accepts = [&](const vector<int> & seq) -> bool {
        long node = 0;
        for (size_t i = 0; i < seq.size(); ++i) {
            auto it = layer_transitions[i][node].find(Integer{seq[i]});
            if (it == layer_transitions[i][node].end())
                return false;
            node = it->second;
        }
        return find(accepting_terminals, node) != accepting_terminals.end();
    };

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [&](vector<int> seq) { return mdd_accepts(seq); }, var_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & [lo, hi] : var_ranges)
        vars.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));
    p.post(MDD{vars, layer_transitions, nodes_per_layer, accepting_terminals});

    auto proof_name = proofs ? make_optional("mdd_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs) -> void
{
    // 3-variable MDD over {0,1,2}.
    // Layer 0 (root): node 0 -> 0 via val 0, val 1, val 2 to layer-1 nodes 0, 1, 2 respectively.
    // Layer 1: each of {0,1,2} -> single layer-2 node depending on value.
    //   node 0 takes val 2 -> node 0 (in layer 2); node 1 takes val 2 -> node 0; node 2 takes val 0 -> node 1.
    // Layer 2: node 0 takes val 0 -> terminal 0; node 1 takes val 0 -> terminal 0.
    // Only accepting terminal is 0; accepts 3 sequences: (0,2,0), (1,2,0), (2,0,0).
    run_mdd_test(proofs, "xcsp3 example",
        {{0, 2}, {0, 2}, {0, 2}},
        {{{{0_i, 0}, {1_i, 1}, {2_i, 2}}},
            {{{2_i, 0}}, {{2_i, 0}}, {{0_i, 1}}},
            {{{0_i, 0}}, {{0_i, 0}}}},
        {1, 3, 2, 1},
        {0});

    // 4-variable boolean MDD: accept iff exactly one 1 appears.
    // Layer i state = number of 1s seen so far (0, 1, 2+). Last state is dead.
    run_mdd_test(proofs, "exactly one 1",
        {{0, 1}, {0, 1}, {0, 1}, {0, 1}},
        {{{{0_i, 0}, {1_i, 1}}},
            {{{0_i, 0}, {1_i, 1}}, {{0_i, 1}, {1_i, 2}}},
            {{{0_i, 0}, {1_i, 1}}, {{0_i, 1}, {1_i, 2}}, {}},
            {{{0_i, 0}, {1_i, 1}}, {{0_i, 1}, {1_i, 2}}, {}}},
        {1, 2, 3, 3, 3},
        {1});

    // Layered MDD with non-uniform layer widths: tests proper per-layer indexing.
    // 3 vars over {0,1,2}.
    // Layer 0: 1 node. Layer 1: 2 nodes. Layer 2: 3 nodes. Layer 3: 1 node (terminal).
    // Layer 0 transitions: val 0 -> L1 node 0; val 1 -> L1 node 1; val 2 -> L1 node 1.
    // Layer 1 transitions: L1 node 0: val 0,1 -> L2 node 0, val 2 -> L2 node 1.
    //                      L1 node 1: val 0 -> L2 node 2.
    // Layer 2 transitions: L2 node 0: val 0 -> terminal; L2 node 1: val 1 -> terminal;
    //                      L2 node 2: val 2 -> terminal.
    run_mdd_test(proofs, "non-uniform widths",
        {{0, 2}, {0, 2}, {0, 2}},
        {{{{0_i, 0}, {1_i, 1}, {2_i, 1}}},
            {{{0_i, 0}, {1_i, 0}, {2_i, 1}}, {{0_i, 2}}},
            {{{0_i, 0}}, {{1_i, 0}}, {{2_i, 0}}}},
        {1, 2, 3, 1},
        {0});

    // GAC-forced pruning: 3 boolean vars; MDD accepts (1,0,1) and (0,1,0) only.
    // After posting at root, both must be free; but for each pair of fixed extremes,
    // GAC should be derivable.
    run_mdd_test(proofs, "two paths",
        {{0, 1}, {0, 1}, {0, 1}},
        {{{{0_i, 0}, {1_i, 1}}},
            {{{1_i, 0}}, {{0_i, 1}}},
            {{{0_i, 0}}, {{1_i, 0}}}},
        {1, 2, 2, 1},
        {0});

    // Unsatisfiable: no accepting terminals.
    run_mdd_test(proofs, "no accepting terminals",
        {{0, 1}, {0, 1}, {0, 1}},
        {{{{0_i, 0}, {1_i, 1}}},
            {{{0_i, 0}, {1_i, 1}}, {{0_i, 1}, {1_i, 0}}},
            {{{0_i, 0}, {1_i, 1}}, {{0_i, 1}, {1_i, 0}}}},
        {1, 2, 2, 2},
        {});

    // Variable domains narrower than the MDD alphabet — must still emit
    // "no transition" constraints over the full alphabet so GAC verifies.
    run_mdd_test(proofs, "narrow domains vs alphabet",
        {{0, 1}, {0, 1}, {0, 1}},
        {{{{0_i, 0}, {1_i, 1}, {2_i, 1}}},
            {{{0_i, 0}, {1_i, 0}, {2_i, 1}}, {{0_i, 0}}},
            {{{0_i, 0}}, {{1_i, 0}}}},
        {1, 2, 2, 1},
        {0});
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
