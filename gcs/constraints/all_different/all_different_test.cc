#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

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
using std::random_device;
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

auto run_all_different_test(bool proofs, const ViewWrapConfig & view_cfg, variant<int, pair<int, int>> v1_range,
    variant<int, pair<int, int>> v2_range, variant<int, pair<int, int>> v3_range, variant<int, pair<int, int>> v4_range,
    variant<int, pair<int, int>> v5_range, variant<int, pair<int, int>> v6_range) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 6);
    // if this crashes your compiler, implement print for variant instead...
    visit(
        [&](auto v1, auto v2, auto v3, auto v4, auto v5, auto v6) {
            print(cerr, "all_different [{}] {} {} {} {} {} {} {}", view_wrap_config_label(view_cfg), v1, v2, v3, v4, v5, v6,
                proofs ? " with proofs:" : ":");
        },
        v1_range, v2_range, v3_range, v4_range, v5_range, v6_range);
    cerr << flush;

    auto is_satisfying = [](int a, int b, int c, int d, int e, int f) {
        return a != b && a != c && a != d && a != e && a != f && b != c && b != d && b != e && b != f && c != d && c != e && c != f && d != e &&
            d != f && e != f;
    };

    set<tuple<int, int, int, int, int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range, v4_range, v5_range, v6_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(0)); }, v1_range);
    auto v2 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(1)); }, v2_range);
    auto v3 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(2)); }, v3_range);
    auto v4 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(3)); }, v4_range);
    auto v5 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(4)); }, v5_range);
    auto v6 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(5)); }, v6_range);
    p.post(AllDifferent{vector<IntegerVariableID>{v1, v2, v3, v4, v5, v6}});

    auto proof_name = proofs ? make_optional("all_different_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, v4, v5, v6});

    check_results(proof_name, expected, actual);
}

// AllDifferent with the same variable in two positions is unsatisfiable
// (the constraint requires `x != x`). Exercise both the GAC and VC
// flavours: the consequence-contradiction path runs the standard
// clique-of-not-equals encoding (which emits a self-contradicting
// half-reified pair for the duplicated variable) and a contradiction
// initialiser that derives false by plain RUP.
auto run_alldiff_dup_test(bool proofs, const vector<vector<int>> & unique_domains, const vector<int> & positions, const string & flavour,
    AllDifferentConsistency level) -> void
{
    print(cerr, "all_different_dup [{}] domains {} positions {}{}", flavour, unique_domains, positions, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    println(cerr, " expecting 0 solutions");

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_domains) {
        vector<Integer> vals;
        for (int v : d)
            vals.push_back(Integer(v));
        unique_vars.push_back(p.create_integer_variable(vals));
    }
    vector<IntegerVariableID> posted_vars;
    for (auto pos : positions)
        posted_vars.push_back(unique_vars[pos]);
    p.post(AllDifferent{posted_vars}.with_consistency(level));

    auto proof_name = proofs ? make_optional("all_different_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars});
    check_results(proof_name, expected, actual);
}

// issue #254: AllDifferent over a degenerate collection — the empty array and
// the single-element array (both trivially satisfiable), plus tiny all-constant
// arrays in both the distinct (SAT) and duplicate (UNSAT) directions. Guards
// against UB on empty containers and proof steps referencing absent variables.
auto run_alldiff_collection_test(bool proofs, const string & label, const vector<variant<int, pair<int, int>>> & specs) -> void
{
    print(cerr, "all_different_collection [{}] {}{}", label, specs, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [](const vector<int> & vs) {
        for (std::size_t i = 0; i < vs.size(); ++i)
            for (std::size_t j = i + 1; j < vs.size(); ++j)
                if (vs[i] == vs[j])
                    return false;
        return true;
    };

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, specs);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & s : specs)
        vars.push_back(visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, s));
    p.post(AllDifferent{vars});

    auto proof_name = proofs ? make_optional("all_different_test_collection") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 6;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "all_different view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    vector<tuple<variant<int, pair<int, int>>, variant<int, pair<int, int>>, variant<int, pair<int, int>>, variant<int, pair<int, int>>,
        variant<int, pair<int, int>>, variant<int, pair<int, int>>>>
        data = {{pair{1, 6}, pair{1, 6}, pair{1, 6}, pair{1, 6}, pair{1, 6}, pair{1, 6}}, //
            {pair{0, 5}, pair{1, 6}, pair{2, 7}, pair{3, 8}, pair{4, 9}, pair{5, 6}},     //
            // issue #108: constants in hall set crash prove_matching_is_too_small
            {pair{-2, 3}, 5, pair{3, 5}, pair{3, 6}, 3, pair{3, 5}}, //
            // issue #108: constants in hall set crash prove_deletion_using_sccs
            {pair{1, 2}, pair{1, 2}, 3, pair{3, 4}, pair{4, 5}, pair{5, 6}}, //
            // issue #254: fully all-constant arguments (genuine
            // ConstantIntegerVariableIDs), both directions.
            {1, 2, 3, 4, 5, 6},  // all distinct constants (tautology)
            {1, 1, 3, 4, 5, 6},  // two equal constants (contradiction)
            {7, 7, 7, 7, 7, 7}}; // all equal constants (contradiction)

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 2, 5), random_bounds(-10, 10, 2, 5), random_bounds(-10, 10, 2, 5),
            random_bounds(-10, 10, 2, 5), random_bounds(-10, 10, 2, 5), random_bounds(-10, 10, 2, 5));

    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 2, 5), random_constant(-10, 10), random_bounds(-10, 10, 2, 5),
            random_bounds(-10, 10, 2, 5), random_bounds(-10, 10, 2, 5), random_bounds(-10, 10, 2, 5));

    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 2, 5), random_constant(-10, 10), random_bounds(-10, 10, 2, 5),
            random_bounds(-10, 10, 2, 5), random_constant(-10, 10), random_bounds(-10, 10, 2, 5));

    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_constant(-10, 10), random_constant(-10, 10), random_constant(-10, 10), random_constant(-10, 10),
            random_constant(-10, 10), random_constant(-10, 10));

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2, r3, r4, r5, r6] : data)
            run_all_different_test(proofs, view_cfg, r1, r2, r3, r4, r5, r6);

        // Duplicate-variable cases for both flavours: smallest non-trivial
        // pair, a duplicate among more variables, and two duplicate runs.
        if (run_dup) {
            for (auto & [unique_domains, positions] : vector<pair<vector<vector<int>>, vector<int>>>{{{{0, 1}}, {0, 0}}, //
                     {{{0, 3}, {0, 3}}, {0, 0, 1}},                                                                      //
                     {{{0, 3}, {0, 3}}, {0, 0, 1, 1}}}) {
                run_alldiff_dup_test(proofs, unique_domains, positions, "gac", consistency::GAC{});
                run_alldiff_dup_test(proofs, unique_domains, positions, "vc", consistency::VC{});
            }

            // Degenerate collections (issue #254).
            run_alldiff_collection_test(proofs, "empty", {});
            run_alldiff_collection_test(proofs, "single_var", {pair{0, 2}});
            run_alldiff_collection_test(proofs, "single_const", {5});
            run_alldiff_collection_test(proofs, "const_distinct", {1, 2, 3});
            run_alldiff_collection_test(proofs, "const_dup", {1, 2, 1});
        }
    }

    return EXIT_SUCCESS;
}
