#include <gcs/constraints/in.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <util/enumerate.hh>

#include <algorithm>
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
using std::set;
using std::string;
using std::tuple;
using std::uniform_int_distribution;
using std::vector;
using std::ranges::find;
using std::ranges::minmax;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

auto run_in_integer_vals_test(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> var_range, vector<int> allowed) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 1);
    print(cerr, "in integer vals [{}] [{},{}] {} {}", view_wrap_config_label(view_cfg), var_range.first, var_range.second, allowed,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int>> expected, actual;
    build_expected(expected, [&](int v) -> bool { return find(allowed, v) != allowed.end(); }, var_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = create_integer_variable_or_constant_with_view(p, var_range, wraps.at(0));
    vector<Integer> vals;
    for (int v : allowed)
        vals.push_back(Integer(v));
    p.post(In{var, vals});

    auto proof_name = proofs ? make_optional("in_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{var});
    check_results(proof_name, expected, actual);
}

auto run_in_const_vars_test(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> var_range, vector<int> allowed) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 1);
    print(cerr, "in const vars [{}] [{},{}] {} {}", view_wrap_config_label(view_cfg), var_range.first, var_range.second, allowed,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int>> expected, actual;
    build_expected(expected, [&](int v) -> bool { return find(allowed, v) != allowed.end(); }, var_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = create_integer_variable_or_constant_with_view(p, var_range, wraps.at(0));
    vector<IntegerVariableID> const_vars;
    for (int v : allowed)
        const_vars.push_back(ConstantIntegerVariableID{Integer(v)});
    p.post(In{var, const_vars});

    auto proof_name = proofs ? make_optional("in_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{var});
    check_results(proof_name, expected, actual);
}

auto run_in_mixed_test(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> var_range, vector<int> const_var_vals, vector<int> int_vals)
    -> void
{
    auto wraps = wraps_for_positions(view_cfg, 1);
    vector<int> all_allowed = const_var_vals;
    all_allowed.insert(all_allowed.end(), int_vals.begin(), int_vals.end());

    print(cerr, "in mixed [{}] [{},{}] const={} ints={} {}", view_wrap_config_label(view_cfg), var_range.first, var_range.second, const_var_vals,
        int_vals, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int>> expected, actual;
    build_expected(expected, [&](int v) -> bool { return find(all_allowed, v) != all_allowed.end(); }, var_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = create_integer_variable_or_constant_with_view(p, var_range, wraps.at(0));
    vector<IntegerVariableID> const_vars;
    for (int v : const_var_vals)
        const_vars.push_back(ConstantIntegerVariableID{Integer(v)});
    vector<Integer> vals;
    for (int v : int_vals)
        vals.push_back(Integer(v));
    p.post(In{var, const_vars, vals});

    auto proof_name = proofs ? make_optional("in_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{var});
    check_results(proof_name, expected, actual);
}

auto run_in_var_list_test(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> var_range, const vector<pair<int, int>> & vars_ranges) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 1);
    print(cerr, "in var list [{}] [{},{}] {} {}", view_wrap_config_label(view_cfg), var_range.first, var_range.second, vars_ranges,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](int v, const vector<int> & w) -> bool {
            for (int x : w)
                if (x == v)
                    return true;
            return false;
        },
        var_range, vars_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = create_integer_variable_or_constant_with_view(p, var_range, wraps.at(0));
    vector<IntegerVariableID> vars;
    for (const auto & [l, u] : vars_ranges)
        vars.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    p.post(In{var, vars});

    auto proof_name = proofs ? make_optional("in_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{var, CheckConsistency::GAC}, pair{vars, CheckConsistency::GAC}});
    check_results(proof_name, expected, actual);
}

auto run_in_var_list_mixed_test(
    bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> var_range, const vector<pair<int, int>> & vars_ranges, vector<int> int_vals) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 1);
    print(cerr, "in mixed var list [{}] [{},{}] {} ints={} {}", view_wrap_config_label(view_cfg), var_range.first, var_range.second, vars_ranges,
        int_vals, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](int v, const vector<int> & w) -> bool {
            for (int x : w)
                if (x == v)
                    return true;
            for (int k : int_vals)
                if (k == v)
                    return true;
            return false;
        },
        var_range, vars_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = create_integer_variable_or_constant_with_view(p, var_range, wraps.at(0));
    vector<IntegerVariableID> vars;
    for (const auto & [l, u] : vars_ranges)
        vars.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    vector<Integer> vals;
    for (int v : int_vals)
        vals.push_back(Integer(v));
    p.post(In{var, vars, vals});

    auto proof_name = proofs ? make_optional("in_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{var, CheckConsistency::GAC}, pair{vars, CheckConsistency::GAC}});
    check_results(proof_name, expected, actual);
}

// The range prunings' bound lemmas only earn their place when what a variable is
// missing is a *hole*: a run outside a variable's declared bounds is already
// contradicted by the model's own domain rows, so unit propagation crosses the
// selector's equality without help and the lemmas are dead weight there. A hole
// is stated by a range literal and nothing else, which is the disjunction RUP
// cannot split -- see justify_not_in_range.hh. The data table above can only
// express contiguous ranges, and a contiguous domain has no interior hole, so
// these rows spell their domains out value by value (#874).
auto run_in_holes_test(bool proofs, const string & label, const vector<int> & var_values, const vector<vector<int>> & source_values) -> void
{
    print(cerr, "in holes [{}] var={} sources={} {}", label, var_values, source_values, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto span = [](const vector<int> & values) {
        auto [lo, hi] = minmax(values);
        return pair{lo, hi};
    };
    auto holds = [](const vector<int> & values, int v) { return find(values, v) != values.end(); };

    vector<pair<int, int>> source_spans;
    for (const auto & values : source_values)
        source_spans.push_back(span(values));

    set<tuple<int, vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](int v, const vector<int> & w) -> bool {
            if (! holds(var_values, v))
                return false;
            for (const auto & [i, x] : enumerate(w))
                if (! holds(source_values.at(i), x))
                    return false;
            return find(w, v) != w.end();
        },
        span(var_values), source_spans);
    println(cerr, " expecting {} solutions", expected.size());

    auto to_integers = [](const vector<int> & values) {
        vector<Integer> result;
        for (auto v : values)
            result.push_back(Integer{v});
        return result;
    };

    Problem p;
    auto var = p.create_integer_variable(to_integers(var_values));
    vector<IntegerVariableID> vars;
    for (const auto & values : source_values)
        vars.push_back(p.create_integer_variable(to_integers(values)));
    p.post(In{var, vars});

    auto proof_name = proofs ? make_optional("in_test_holes_" + label) : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{var, CheckConsistency::GAC}, pair{vars, CheckConsistency::GAC}});
    check_results(proof_name, expected, actual);
}

auto run_in_self_reference_test(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> var_range) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 1);
    print(cerr, "in self [{}] [{},{}] {}", view_wrap_config_label(view_cfg), var_range.first, var_range.second, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int>> expected, actual;
    build_expected(expected, [&](int) -> bool { return true; }, var_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = create_integer_variable_or_constant_with_view(p, var_range, wraps.at(0));
    p.post(In{var, vector<IntegerVariableID>{var}});

    auto proof_name = proofs ? make_optional("in_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{var});
    check_results(proof_name, expected, actual);
}

auto run_all_holes_tests(bool proofs) -> void
{
    auto contiguous = [](int lo, int hi) {
        vector<int> result;
        for (int v = lo; v <= hi; ++v)
            result.push_back(v);
        return result;
    };

    // Step 1, the run coming off var. One source misses [4, 6] because of a hole
    // and the other because of its bounds, so the two lemma pairs are exercised
    // in the one conclusion and only one of them is doing anything.
    run_in_holes_test(proofs, "step1_source_hole", contiguous(0, 9), {{0, 1, 2, 3, 7, 8, 9}, {8, 9}});
    // Both sources miss it by a hole, at different distances from the run.
    run_in_holes_test(proofs, "step1_all_holes", contiguous(0, 9), {{0, 1, 2, 3, 8, 9}, {0, 4, 8, 9}});
    // Step 3, the run coming off the single supporting source. var's hole is
    // [3, 5], the second source misses dom(var) entirely so it is not a
    // supporter, and the first has to lose exactly the hole.
    run_in_holes_test(proofs, "step3_var_hole", {0, 1, 2, 6, 7, 8}, {contiguous(0, 8), {10, 11}});
}

auto run_all_tests(bool proofs, const ViewWrapConfig & view_cfg) -> void
{
    // In with integer values
    run_in_integer_vals_test(proofs, view_cfg, {1, 5}, {1, 3, 5});       // alternate values
    run_in_integer_vals_test(proofs, view_cfg, {1, 5}, {2, 4});          // even values only
    run_in_integer_vals_test(proofs, view_cfg, {1, 5}, {1, 2, 3, 4, 5}); // all values: no filtering
    run_in_integer_vals_test(proofs, view_cfg, {1, 5}, {3});             // single value
    run_in_integer_vals_test(proofs, view_cfg, {1, 5}, {7, 8, 9});       // all outside domain: unsat
    run_in_integer_vals_test(proofs, view_cfg, {1, 5}, {2, 5, 8});       // some outside domain: filtered
    run_in_integer_vals_test(proofs, view_cfg, {-3, 3}, {-2, 0, 2});     // negative values
    run_in_integer_vals_test(proofs, view_cfg, {1, 5}, {1, 1, 3, 3});    // duplicates in allowed list

    // In with constant IntegerVariableIDs: same semantics as integer values
    run_in_const_vars_test(proofs, view_cfg, {1, 5}, {1, 3, 5});
    run_in_const_vars_test(proofs, view_cfg, {1, 5}, {7, 8, 9}); // all outside domain: unsat
    run_in_const_vars_test(proofs, view_cfg, {-3, 3}, {-2, 0, 2});

    // In with mixed constant vars and integer values
    run_in_mixed_test(proofs, view_cfg, {1, 6}, {1, 3}, {5}); // {1,3} from vars, {5} from vals
    run_in_mixed_test(proofs, view_cfg, {1, 6}, {2, 4}, {6});

    // In with non-constant variable lists (the case the old implementation didn't handle)
    run_in_var_list_test(proofs, view_cfg, {1, 5}, {{1, 3}, {3, 5}});         // overlapping
    run_in_var_list_test(proofs, view_cfg, {1, 5}, {{2, 2}, {4, 4}});         // singletons (= constants)
    run_in_var_list_test(proofs, view_cfg, {1, 5}, {{1, 5}});                 // single supporter, var = V_0
    run_in_var_list_test(proofs, view_cfg, {1, 4}, {{1, 4}, {1, 4}, {1, 4}}); // all alike
    run_in_var_list_test(proofs, view_cfg, {2, 5}, {{1, 3}, {4, 6}});         // disjoint vars covering var range
    run_in_var_list_test(proofs, view_cfg, {1, 6}, {{1, 2}, {5, 6}});         // disjoint vars, var has middle gap forced
    run_in_var_list_test(proofs, view_cfg, {-2, 2}, {{-1, 0}, {0, 1}});       // negatives + zero overlap

    // Single supporter case (forces filtering of V_i to dom(var))
    run_in_var_list_test(proofs, view_cfg, {2, 4}, {{1, 5}, {7, 9}}); // only V_0 overlaps; V_0 gets pruned to {2,3,4}

    // Rows that reach the range prunings (#874) at all, which needs a *run* of
    // at least two values to remove: a width-one run canonicalises to the same
    // != literal and stays on the per-value path, and every row above happens to
    // leave only those. Deterministic rather than left to the random sweep
    // below, so the range path is entered at a fixed seed rather than by luck.
    // What makes its *lemmas* load-bearing is a hole, which needs domains the
    // table cannot spell -- see run_all_holes_tests.
    run_in_var_list_test(proofs, view_cfg, {1, 8}, {{1, 2}, {7, 8}});       // step 1, one interior run: var loses 3..6
    run_in_var_list_test(proofs, view_cfg, {1, 8}, {{4, 5}});               // step 1, a run at each end, one selector to rule out
    run_in_var_list_test(proofs, view_cfg, {3, 4}, {{1, 8}, {6, 9}});       // step 3: V_1 misses var, so V_0 loses 1..2 and 5..8
    run_in_var_list_mixed_test(proofs, view_cfg, {1, 9}, {{2, 3}}, {6, 7}); // both paths at once: runs 1..1, 4..5 and 8..9

    // Mixed with non-constant vars + constants
    run_in_var_list_mixed_test(proofs, view_cfg, {1, 5}, {{2, 3}}, {5}); // V_0 in {2,3}, plus 5
    run_in_var_list_mixed_test(proofs, view_cfg, {1, 5}, {{1, 5}}, {});  // empty constants

    // Self-reference: trivially satisfied
    run_in_self_reference_test(proofs, view_cfg, {1, 5});
    run_in_self_reference_test(proofs, view_cfg, {-2, 2});

    // Degenerate collections (issue #254): an In with no supporting values at
    // all is unsatisfiable and must be handled cleanly (no UB on the empty
    // value/var lists), across every overload.
    run_in_integer_vals_test(proofs, view_cfg, {1, 5}, {});       // empty value list: unsat
    run_in_const_vars_test(proofs, view_cfg, {1, 5}, {});         // empty const-var list: unsat
    run_in_var_list_test(proofs, view_cfg, {1, 5}, {});           // empty supporter list: unsat
    run_in_var_list_mixed_test(proofs, view_cfg, {1, 5}, {}, {}); // both empty: unsat

    // Fixed (singleton-domain) variable against a constant value set, both
    // directions: the value is present (tautology) or absent (contradiction).
    run_in_integer_vals_test(proofs, view_cfg, {3, 3}, {1, 3, 5}); // 3 in set: tautology
    run_in_integer_vals_test(proofs, view_cfg, {2, 2}, {1, 3, 5}); // 2 not in set: contradiction
    run_in_const_vars_test(proofs, view_cfg, {4, 4}, {4, 5, 6});   // 4 in const-var set: tautology
    run_in_const_vars_test(proofs, view_cfg, {7, 7}, {4, 5, 6});   // 7 not in set: contradiction
}

auto run_random_tests(bool proofs, const ViewWrapConfig & view_cfg, mt19937 & rand) -> void
{
    // Small random sweep. Each shape gets 5 instances. Brute-force cost is
    // O(|dom(var)| * prod(|dom(V_i)|)) per case; on these bounds (var up to
    // width 5, var list up to 3 entries width 4) that's well under 1k
    // combinations per case, so VeriPB stays fast.
    uniform_int_distribution lo_dist{-3, 5};
    uniform_int_distribution width_dist{1, 4};
    uniform_int_distribution count_dist{1, 4};
    uniform_int_distribution val_dist{-3, 8};
    uniform_int_distribution n_vars_dist{1, 3};

    auto random_pair = [&]() {
        int lo = lo_dist(rand);
        return pair{lo, lo + width_dist(rand)};
    };
    auto random_vals = [&](int n) {
        vector<int> vs;
        for (int i = 0; i < n; ++i)
            vs.push_back(val_dist(rand));
        return vs;
    };

    for (int x = 0; x < 5; ++x)
        run_in_integer_vals_test(proofs, view_cfg, random_pair(), random_vals(count_dist(rand)));

    for (int x = 0; x < 5; ++x)
        run_in_const_vars_test(proofs, view_cfg, random_pair(), random_vals(count_dist(rand)));

    for (int x = 0; x < 5; ++x) {
        vector<pair<int, int>> ranges;
        int n = n_vars_dist(rand);
        for (int i = 0; i < n; ++i)
            ranges.push_back(random_pair());
        run_in_var_list_test(proofs, view_cfg, random_pair(), ranges);
    }

    for (int x = 0; x < 5; ++x) {
        vector<pair<int, int>> ranges;
        int n = n_vars_dist(rand);
        for (int i = 0; i < n; ++i)
            ranges.push_back(random_pair());
        run_in_var_list_mixed_test(proofs, view_cfg, random_pair(), ranges, random_vals(count_dist(rand)));
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Only the primary `var` of each In variant is wrapped; the inner
    // vars vector of run_in_var_list_test is not in the sweep.
    constexpr int n_positions = 1;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "in view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    mt19937 rand(*get_seed());

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs, view_cfg);
        // Bare handles only: a view has no range literal (#882), so a wrapped run
        // takes the per-value path and these rows would say nothing about the
        // lemmas they exist for.
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions))
            run_all_holes_tests(proofs);
        run_random_tests(proofs, view_cfg, rand);
    }

    return EXIT_SUCCESS;
}
