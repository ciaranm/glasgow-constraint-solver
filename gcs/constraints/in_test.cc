#include <gcs/constraints/in.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
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

auto run_in_integer_vals_test(bool proofs, pair<int, int> var_range, vector<int> allowed) -> void
{
    print(cerr, "in integer vals [{},{}] {} {}", var_range.first, var_range.second, allowed, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int>> expected, actual;
    build_expected(expected, [&](int v) -> bool { return find(allowed, v) != allowed.end(); }, var_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = p.create_integer_variable(Integer(var_range.first), Integer(var_range.second));
    vector<Integer> vals;
    for (int v : allowed)
        vals.push_back(Integer(v));
    p.post(In{var, vals});

    auto proof_name = proofs ? make_optional("in_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{var});
    check_results(proof_name, expected, actual);
}

auto run_in_const_vars_test(bool proofs, pair<int, int> var_range, vector<int> allowed) -> void
{
    print(cerr, "in const vars [{},{}] {} {}", var_range.first, var_range.second, allowed, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int>> expected, actual;
    build_expected(expected, [&](int v) -> bool { return find(allowed, v) != allowed.end(); }, var_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = p.create_integer_variable(Integer(var_range.first), Integer(var_range.second));
    vector<IntegerVariableID> const_vars;
    for (int v : allowed)
        const_vars.push_back(ConstantIntegerVariableID{Integer(v)});
    p.post(In{var, const_vars});

    auto proof_name = proofs ? make_optional("in_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{var});
    check_results(proof_name, expected, actual);
}

auto run_in_mixed_test(bool proofs, pair<int, int> var_range, vector<int> const_var_vals, vector<int> int_vals) -> void
{
    vector<int> all_allowed = const_var_vals;
    all_allowed.insert(all_allowed.end(), int_vals.begin(), int_vals.end());

    print(cerr, "in mixed [{},{}] const={} ints={} {}", var_range.first, var_range.second, const_var_vals, int_vals, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int>> expected, actual;
    build_expected(expected, [&](int v) -> bool { return find(all_allowed, v) != all_allowed.end(); }, var_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = p.create_integer_variable(Integer(var_range.first), Integer(var_range.second));
    vector<IntegerVariableID> const_vars;
    for (int v : const_var_vals)
        const_vars.push_back(ConstantIntegerVariableID{Integer(v)});
    vector<Integer> vals;
    for (int v : int_vals)
        vals.push_back(Integer(v));
    p.post(In{var, const_vars, vals});

    auto proof_name = proofs ? make_optional("in_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{var});
    check_results(proof_name, expected, actual);
}

auto run_in_var_list_test(bool proofs, pair<int, int> var_range, const vector<pair<int, int>> & vars_ranges) -> void
{
    print(cerr, "in var list [{},{}] {} {}", var_range.first, var_range.second, vars_ranges, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, vector<int>>> expected, actual;
    build_expected(expected, [&](int v, const vector<int> & w) -> bool {
        for (int x : w)
            if (x == v)
                return true;
        return false; }, var_range, vars_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = p.create_integer_variable(Integer(var_range.first), Integer(var_range.second));
    vector<IntegerVariableID> vars;
    for (const auto & [l, u] : vars_ranges)
        vars.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    p.post(In{var, vars});

    auto proof_name = proofs ? make_optional("in_test") : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual,
        tuple{pair{var, CheckConsistency::GAC}, pair{vars, CheckConsistency::GAC}});
    check_results(proof_name, expected, actual);
}

auto run_in_var_list_mixed_test(bool proofs, pair<int, int> var_range, const vector<pair<int, int>> & vars_ranges, vector<int> int_vals) -> void
{
    print(cerr, "in mixed var list [{},{}] {} ints={} {}", var_range.first, var_range.second, vars_ranges, int_vals, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, vector<int>>> expected, actual;
    build_expected(expected, [&](int v, const vector<int> & w) -> bool {
        for (int x : w)
            if (x == v)
                return true;
        for (int k : int_vals)
            if (k == v)
                return true;
        return false; }, var_range, vars_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = p.create_integer_variable(Integer(var_range.first), Integer(var_range.second));
    vector<IntegerVariableID> vars;
    for (const auto & [l, u] : vars_ranges)
        vars.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    vector<Integer> vals;
    for (int v : int_vals)
        vals.push_back(Integer(v));
    p.post(In{var, vars, vals});

    auto proof_name = proofs ? make_optional("in_test") : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual,
        tuple{pair{var, CheckConsistency::GAC}, pair{vars, CheckConsistency::GAC}});
    check_results(proof_name, expected, actual);
}

auto run_in_self_reference_test(bool proofs, pair<int, int> var_range) -> void
{
    print(cerr, "in self [{},{}] {}", var_range.first, var_range.second, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int>> expected, actual;
    build_expected(expected, [&](int) -> bool { return true; }, var_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = p.create_integer_variable(Integer(var_range.first), Integer(var_range.second));
    p.post(In{var, vector<IntegerVariableID>{var}});

    auto proof_name = proofs ? make_optional("in_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{var});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs) -> void
{
    // In with integer values
    run_in_integer_vals_test(proofs, {1, 5}, {1, 3, 5});       // alternate values
    run_in_integer_vals_test(proofs, {1, 5}, {2, 4});          // even values only
    run_in_integer_vals_test(proofs, {1, 5}, {1, 2, 3, 4, 5}); // all values: no filtering
    run_in_integer_vals_test(proofs, {1, 5}, {3});             // single value
    run_in_integer_vals_test(proofs, {1, 5}, {7, 8, 9});       // all outside domain: unsat
    run_in_integer_vals_test(proofs, {1, 5}, {2, 5, 8});       // some outside domain: filtered
    run_in_integer_vals_test(proofs, {-3, 3}, {-2, 0, 2});     // negative values
    run_in_integer_vals_test(proofs, {1, 5}, {1, 1, 3, 3});    // duplicates in allowed list

    // In with constant IntegerVariableIDs: same semantics as integer values
    run_in_const_vars_test(proofs, {1, 5}, {1, 3, 5});
    run_in_const_vars_test(proofs, {1, 5}, {7, 8, 9}); // all outside domain: unsat
    run_in_const_vars_test(proofs, {-3, 3}, {-2, 0, 2});

    // In with mixed constant vars and integer values
    run_in_mixed_test(proofs, {1, 6}, {1, 3}, {5}); // {1,3} from vars, {5} from vals
    run_in_mixed_test(proofs, {1, 6}, {2, 4}, {6});

    // In with non-constant variable lists (the case the old implementation didn't handle)
    run_in_var_list_test(proofs, {1, 5}, {{1, 3}, {3, 5}});         // overlapping
    run_in_var_list_test(proofs, {1, 5}, {{2, 2}, {4, 4}});         // singletons (= constants)
    run_in_var_list_test(proofs, {1, 5}, {{1, 5}});                 // single supporter, var = V_0
    run_in_var_list_test(proofs, {1, 4}, {{1, 4}, {1, 4}, {1, 4}}); // all alike
    run_in_var_list_test(proofs, {2, 5}, {{1, 3}, {4, 6}});         // disjoint vars covering var range
    run_in_var_list_test(proofs, {1, 6}, {{1, 2}, {5, 6}});         // disjoint vars, var has middle gap forced
    run_in_var_list_test(proofs, {-2, 2}, {{-1, 0}, {0, 1}});       // negatives + zero overlap

    // Single supporter case (forces filtering of V_i to dom(var))
    run_in_var_list_test(proofs, {2, 4}, {{1, 5}, {7, 9}}); // only V_0 overlaps; V_0 gets pruned to {2,3,4}

    // Mixed with non-constant vars + constants
    run_in_var_list_mixed_test(proofs, {1, 5}, {{2, 3}}, {5}); // V_0 in {2,3}, plus 5
    run_in_var_list_mixed_test(proofs, {1, 5}, {{1, 5}}, {});  // empty constants

    // Self-reference: trivially satisfied
    run_in_self_reference_test(proofs, {1, 5});
    run_in_self_reference_test(proofs, {-2, 2});
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
