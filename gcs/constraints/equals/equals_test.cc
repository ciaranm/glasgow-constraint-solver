#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::function;
using std::is_same_v;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::set;
using std::string;
using std::tuple;
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

template <typename Constraint_>
auto run_equals_test(const string & which, bool proofs, const ViewWrapConfig & view_cfg, variant<int, pair<int, int>> v1_range,
    variant<int, pair<int, int>> v2_range, const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2);
    visit([&](auto v1,
              auto v2) { print(cerr, "equals {} [{}] {} {} {}", which, view_wrap_config_label(view_cfg), v1, v2, proofs ? " with proofs:" : ":"); },
        v1_range, v2_range);
    cerr << flush;

    pair<int, int> v3_range{0, 1};
    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(0)); }, v1_range);
    auto v2 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(1)); }, v2_range);
    auto v3 = p.create_integer_variable(0_i, 1_i);
    if constexpr (is_same_v<Constraint_, Equals>) {
        p.post(Constraint_{v1, v2});
    }
    else if constexpr (is_same_v<Constraint_, NotEquals>) {
        p.post(Constraint_{v1, v2});
    }
    else {
        p.post(Constraint_{v1, v2, v3 == 1_i});
    }

    auto proof_name = proofs ? make_optional("equals_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: post a constraint with the same handle in both
// variable slots. Consistency is intentionally not checked: a GAC
// algorithm for distinct variables doesn't generally yield GAC under
// aliasing, and fixing it varies in difficulty per constraint. We
// verify the solution set and the proof only.
template <typename Constraint_>
auto run_dup_equals_test(const string & filename_tag, bool proofs, pair<int, int> x_range, const function<auto(int, int)->bool> & is_satisfying)
    -> void
{
    print(cerr, "equals dup {} {} {}", filename_tag, x_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    pair<int, int> c_range{0, 1};
    set<tuple<int, int>> expected, actual;
    build_expected(expected, is_satisfying, x_range, c_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second));
    auto c = p.create_integer_variable(0_i, 1_i);
    if constexpr (is_same_v<Constraint_, Equals> || is_same_v<Constraint_, NotEquals>) {
        p.post(Constraint_{x, x});
    }
    else {
        p.post(Constraint_{x, x, c == 1_i});
    }

    auto proof_name = proofs ? make_optional("equals_test_dup_" + filename_tag) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x, c});

    check_results(proof_name, expected, actual);
}

auto run_no_overlap_equals_test(bool proofs) -> void
{
    print(cerr, "no overlap equals {}", proofs ? " with proofs:" : ":");
    cerr << flush;

    pair<int, int> x_range{1, 10};
    pair<int, int> y_range{1, 10};
    pair<int, int> z_range{0, 1};
    pair<int, int> c_range{0, 1};
    set<tuple<int, int, int, int>> expected, actual;
    build_expected(
        expected,
        [](int x, int y, int z, int c) -> bool {
            if (x == 4 && c != 0)
                return false;
            if (x == 5 && c != 0)
                return false;
            if (x == 6 && c != 0)
                return false;
            if (x == 9 && c != 0)
                return false;
            if (x == 10 && c != 0)
                return false;

            if (y == 1 && c != 0)
                return false;
            if (y == 2 && c != 0)
                return false;
            if (y == 3 && c != 0)
                return false;
            if (y == 6 && c != 0)
                return false;
            if (y == 7 && c != 0)
                return false;
            if (y == 8 && c != 0)
                return false;

            if (z == 1) {
                if (x != y)
                    return false;
            }
            return true;
        },
        x_range, y_range, z_range, c_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(1_i, 10_i);
    auto y = p.create_integer_variable(1_i, 10_i);
    auto z = p.create_integer_variable(0_i, 1_i);
    auto c = p.create_integer_variable(0_i, 1_i);
    p.post(EqualsIf{x, y, z == 1_i});

    p.post(EqualsIf{c, 0_c, x == 4_i});
    p.post(EqualsIf{c, 0_c, x == 5_i});
    p.post(EqualsIf{c, 0_c, x == 6_i});
    p.post(EqualsIf{c, 0_c, x == 9_i});
    p.post(EqualsIf{c, 0_c, x == 10_i});

    p.post(EqualsIf{c, 0_c, y == 1_i});
    p.post(EqualsIf{c, 0_c, y == 2_i});
    p.post(EqualsIf{c, 0_c, y == 3_i});
    p.post(EqualsIf{c, 0_c, y == 6_i});
    p.post(EqualsIf{c, 0_c, y == 7_i});
    p.post(EqualsIf{c, 0_c, y == 8_i});

    auto proof_name = proofs ? make_optional("equals_test") : nullopt;
    // x, y, z are each GAC (a single EqualsIf is GAC, and c=1 does propagate
    // x != 4 etc. via the contrapositive). But c is only network-GAC: c=1 is
    // unsupported at z=1 because x==y combined with *all* the c -> x not in {...}
    // / c -> y not in {...} implications leaves no common value -- a deduction
    // across all 13 posted constraints that no individual EqualsIf propagator
    // can make (GAC of a conjunction != conjunction of GAC). So c is None.
    solve_for_tests_checking_consistency(p, proof_name, expected, actual,
        tuple{pair{x, CheckConsistency::GAC}, pair{y, CheckConsistency::GAC}, pair{z, CheckConsistency::GAC}, pair{c, CheckConsistency::None}});

    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Single-position config that names a position the constraint doesn't
    // have collapses to "all bare", which the baseline (no flags) already
    // covers. Skip with a success exit so ctest sees it as benign.
    constexpr int n_positions = 2;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "equals view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    vector<pair<variant<int, pair<int, int>>, variant<int, pair<int, int>>>> data = {
        {pair{2, 5}, pair{1, 6}},     //
        {pair{1, 6}, pair{2, 5}},     //
        {pair{1, 3}, pair{1, 3}},     //
        {pair{1, 5}, pair{6, 8}},     //
        {pair{1, 1}, pair{2, 4}},     //
        {pair{-2, -2}, pair{-2, -1}}, //
        {pair{1, 3}, pair{5, 8}},     //
        {pair{4, 13}, pair{3, 16}},   //
        {pair{-2, 4}, pair{-8, 7}},   //
        {pair{-7, 3}, pair{-10, 5}},  //
        // issue #254: genuine all-constant operands (ConstantIntegerVariableID),
        // both directions. Each Equals/NotEquals (and reified) mode is computed
        // from build_expected: 4==4 holds, 4==5 does not.
        {4, 4},  //
        {4, 5},  //
        {-3, -3} //
    };

    mt19937 rand(*get_seed());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_constant(-10, 10), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_constant(-10, 10));

    // no_overlap_equals_test fixes its own variable construction and isn't
    // currently part of the view sweep, so only run it for the baseline.
    bool run_no_overlap = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    // Bare-handle dup ranges. Skipped under the view-wrap sweep (which
    // mutates positional view-wraps in ways that aren't aliasing-aware).
    vector<pair<int, int>> dup_data = {
        {0, 0}, {0, 1}, {0, 5}, {-3, 3}, {2, 5} //
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        if (run_no_overlap)
            run_no_overlap_equals_test(proofs);
        for (auto & [r1, r2] : data) {
            run_equals_test<Equals>("equals", proofs, view_cfg, r1, r2, [](int a, int b, int) { return a == b; });
            run_equals_test<EqualsIf>("equals if", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (! f) || (a == b); });
            run_equals_test<EqualsIff>("equals iff", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (a == b) == f; });
            run_equals_test<NotEquals>("not equals", proofs, view_cfg, r1, r2, [](int a, int b, int) { return a != b; });
            run_equals_test<NotEqualsIf>("not equals if", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (! f) || (a != b); });
            run_equals_test<NotEqualsIff>("not equals iff", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (a != b) == f; });
        }
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions))
            for (auto & x_range : dup_data) {
                run_dup_equals_test<Equals>("equals", proofs, x_range, [](int, int) { return true; });
                run_dup_equals_test<EqualsIf>("equals_if", proofs, x_range, [](int, int) { return true; });
                run_dup_equals_test<EqualsIff>("equals_iff", proofs, x_range, [](int, int c) { return c == 1; });
                run_dup_equals_test<NotEqualsIff>("notequals_iff", proofs, x_range, [](int, int c) { return c == 0; });
                // NotEqualsIf(x, x, c) ≡ c → x ≠ x ≡ ¬c. Was Bucket B
                // (propagator silent on alias) — fixed by alias check in
                // ReifiedEquals' infer_cond_when_undecided.
                run_dup_equals_test<NotEqualsIf>("notequals_if", proofs, x_range, [](int, int c) { return c == 0; });
            }
    }

    {
        // NotEquals on aliased operands is trivially unsat; reject at
        // construction rather than discovering after search.
        Problem p;
        auto x = p.create_integer_variable(Integer{0}, Integer{3});
        try {
            p.post(NotEquals{x, x});
            cerr << "expected NotEquals(x,x) to throw InvalidProblemDefinitionException" << '\n';
            return EXIT_FAILURE;
        }
        catch (const InvalidProblemDefinitionException &) {
        }
    }

    return EXIT_SUCCESS;
}
