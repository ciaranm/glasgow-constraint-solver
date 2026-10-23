#include <gcs/constraints/innards/constraints_test_utils.hh>
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
#include <variant>
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
using std::move;
using std::nullopt;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::unordered_map;
using std::variant;
using std::vector;
using std::ranges::find;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

// Each position is either a range, declared with create_integer_variable(lo, hi), or
// a value list, declared from its values. The two are encoded differently (a value
// list gets an at-least-one row over its values, a range does not), and some of the
// scaffold's lines are RUP for one and not the other, so the tests need both.
using VarSpec = variant<int, pair<int, int>, vector<int>>;

auto run_regular_bacchus_test(bool proofs, const string & desc, const vector<VarSpec> & var_specs, long num_states,
    vector<unordered_map<Integer, long>> transitions, vector<long> final_states) -> void
{
    print(cerr, "regular_bacchus {} {} vars{}", desc, var_specs.size(), proofs ? " with proofs:" : ":");
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
    build_expected(expected, [&](vector<int> seq) { return dfa_accepts(seq); }, var_specs);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & spec : var_specs) {
        if (auto range = std::get_if<pair<int, int>>(&spec))
            vars.push_back(p.create_integer_variable(Integer(range->first), Integer(range->second)));
        else if (auto values = std::get_if<vector<int>>(&spec)) {
            vector<Integer> vals;
            for (auto v : *values)
                vals.push_back(Integer(v));
            vars.push_back(p.create_integer_variable(vals));
        }
        else
            vars.push_back(ConstantIntegerVariableID{Integer(std::get<int>(spec))});
    }
    p.post(Regular{vars, num_states, transitions, final_states}.with_proof_strategy(proof_strategy::Bacchus{}));

    auto proof_name = proofs ? make_optional("regular_bacchus_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

auto run_regular_bacchus_test(bool proofs, const string & desc, const vector<pair<int, int>> & var_ranges, long num_states,
    vector<unordered_map<Integer, long>> transitions, vector<long> final_states) -> void
{
    run_regular_bacchus_test(proofs, desc, vector<VarSpec>{var_ranges.begin(), var_ranges.end()}, num_states, move(transitions), move(final_states));
}

auto run_all_tests(bool proofs) -> void
{
    run_regular_bacchus_test(proofs, "even zeros", {{0, 1}, {0, 1}, {0, 1}}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {0});

    run_regular_bacchus_test(proofs, "no consecutive 0s", {{0, 1}, {0, 1}, {0, 1}, {0, 1}}, 2, {{{0_i, 1}, {1_i, 0}}, {{1_i, 0}}}, {0, 1});

    run_regular_bacchus_test(
        proofs, "contains 2", {{0, 2}, {0, 2}, {0, 2}}, 2, {{{0_i, 0}, {1_i, 0}, {2_i, 1}}, {{0_i, 1}, {1_i, 1}, {2_i, 1}}}, {1});

    run_regular_bacchus_test(
        proofs, "contains 2, last forced to 2", {{0, 1}, {0, 1}, {0, 2}}, 2, {{{0_i, 0}, {1_i, 0}, {2_i, 1}}, {{0_i, 1}, {1_i, 1}, {2_i, 1}}}, {1});

    run_regular_bacchus_test(proofs, "all same", {{0, 1}, {0, 1}, {0, 1}, {0, 1}}, 4, {{{0_i, 1}, {1_i, 2}}, {{0_i, 1}}, {{1_i, 2}}, {}}, {1, 2});

    run_regular_bacchus_test(proofs, "no final states", {{0, 1}, {0, 1}, {0, 1}}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {});

    run_regular_bacchus_test(proofs, "domain excludes accepting paths", {{0, 1}, {0, 1}, {0, 1}}, 2,
        {{{0_i, 0}, {1_i, 0}, {2_i, 1}}, {{0_i, 1}, {1_i, 1}, {2_i, 1}}}, {1});

    // The empty word is accepted exactly when the start state 0 is final (#1329).
    run_regular_bacchus_test(proofs, "empty seq accepted", vector<pair<int, int>>{}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {0});
    run_regular_bacchus_test(proofs, "empty seq rejected", vector<pair<int, int>>{}, 2, {{{0_i, 1}, {1_i, 0}}, {{0_i, 0}, {1_i, 1}}}, {1});

    // The next three are each rejected without the scaffold's unit lines (#1331),
    // whatever the branching. Here state 1 has no outgoing transition, and the
    // instance is unsatisfiable: the root backtrack needs a unit to say state 1 is
    // ruled out.
    run_regular_bacchus_test(proofs, "state with no outgoing transition", vector<VarSpec>{vector<int>{-2, 0, 1, 2}, pair{-1, 2}}, 2,
        {{{-1_i, 1}, {0_i, 1}, {1_i, 1}}, {}}, {1});
    // Two final states, so unit propagation cannot get from the accept row to a
    // state at the last layer being false. Either the unit for the non-final state
    // 2 there or the unit for state 0, which is final but which no transition leads
    // to, closes the backtrack after the one solution.
    run_regular_bacchus_test(proofs, "non-final state at the last layer", vector<VarSpec>{vector<int>{-1, 3}, pair{0, 2}}, 3,
        {{{0_i, 2}, {1_i, 2}, {3_i, 2}}, {{-1_i, 2}, {2_i, 1}, {3_i, 2}}, {{0_i, 1}, {1_i, 2}, {2_i, 2}}}, {0, 1});
    // States 1 and 2 have no outgoing transitions, and the incoming at-least-one for
    // state 0 at layer 2 is not RUP without their no-outgoing units at layer 1. That
    // line is in the scaffold itself, so without them this one is rejected at every
    // assertion level, not only at Off.
    run_regular_bacchus_test(proofs, "incoming at-least-one over states with no transitions",
        vector<VarSpec>{vector<int>{-2, -1, 0, 1}, vector<int>{-2, -1, 0}}, 3, {{{-2_i, 2}, {-1_i, 0}, {0_i, 1}}, {}, {}}, {0, 1});
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs);
    }

    return EXIT_SUCCESS;
}
