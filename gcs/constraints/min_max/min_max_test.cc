#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <util/enumerate.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
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

auto run_min_max_test(bool proofs, const ViewWrapConfig & view_cfg, bool min, variant<int, pair<int, int>> result_range,
    const vector<variant<int, pair<int, int>>> & array_range) -> void
{
    // Position 0 = result; positions 1..N = array elements.
    int n_positions = 1 + static_cast<int>(array_range.size());
    auto wraps = wraps_for_positions(view_cfg, n_positions);
    visit(
        [&](auto r) {
            print(cerr, "{} [{}] {} {} {}", min ? "min" : "max", view_wrap_config_label(view_cfg), r, array_range, proofs ? " with proofs:" : ":");
        },
        result_range);
    cerr << flush;

    auto is_satisfying = [&](int r, const vector<int> & a) {
        return (! a.empty()) && (min ? (*min_element(a.begin(), a.end()) == r) : (*max_element(a.begin(), a.end()) == r));
    };

    set<pair<int, vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, result_range, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto result = visit([&](auto r) { return create_integer_variable_or_constant_with_view(p, r, wraps.at(0)); }, result_range);
    vector<IntegerVariableID> array;
    for (std::size_t i = 0; i < array_range.size(); ++i)
        array.push_back(visit([&](auto e) { return create_integer_variable_or_constant_with_view(p, e, wraps.at(i + 1)); }, array_range[i]));
    if (min)
        p.post(ArrayMin{array, result});
    else
        p.post(ArrayMax{array, result});

    auto proof_name = proofs ? make_optional("min_max_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_consistency(
        p, proof_name, expected, actual, tuple{pair{result, CheckConsistency::GAC}, pair{array, CheckConsistency::GAC}});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: Min/Max with the same handle in several array
// positions, or the result var aliasing an array entry. Consistency
// isn't checked on dup runs; see tmp/duplicate_var_audit.md.
auto run_dup_min_max_test(bool proofs, bool min, const string & label, const vector<pair<int, int>> & unique_domains,
    const vector<int> & array_positions, int result_position_in_unique, pair<int, int> result_range) -> void
{
    print(cerr, "{} dup {} unique_doms={} positions={} result_pos={}{}", min ? "min" : "max", label, unique_domains, array_positions,
        result_position_in_unique, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, int>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & unique_vals, int r) -> bool {
            vector<int> array_vals;
            for (auto pos : array_positions)
                array_vals.push_back(unique_vals.at(pos));
            if (array_vals.empty())
                return false;
            int expected_r = min ? *min_element(array_vals.begin(), array_vals.end()) : *max_element(array_vals.begin(), array_vals.end());
            if (r != expected_r)
                return false;
            if (result_position_in_unique >= 0)
                return unique_vals.at(result_position_in_unique) == r;
            return true;
        },
        unique_domains, result_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> array;
    for (auto pos : array_positions)
        array.push_back(unique_vars.at(pos));
    IntegerVariableID result = (result_position_in_unique >= 0)
        ? unique_vars.at(result_position_in_unique)
        : p.create_integer_variable(Integer(result_range.first), Integer(result_range.second));
    if (min)
        p.post(ArrayMin{array, result});
    else
        p.post(ArrayMax{array, result});

    auto proof_name = proofs ? make_optional((min ? string{"min_max_test_min_dup_"} : string{"min_max_test_max_dup_"}) + label) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars, result});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Position 0 = result; positions 1..5 = up to 5 array entries.
    constexpr int n_positions = 6;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "min_max view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    using ArrayEntry = variant<int, pair<int, int>>;
    vector<tuple<variant<int, pair<int, int>>, vector<ArrayEntry>>> data = {              // Singleton: result must equal the sole element.
        {pair{1, 5}, {pair{2, 4}}},                                                       //
        {3, {pair{0, 5}}},                                                                //
        {pair{1, 2}, {pair{1, 2}, pair{1, 2}}},                                           //
        {pair{1, 2}, {pair{1, 2}, pair{1, 2}, pair{1, 2}}},                               //
        {pair{0, 4}, {pair{1, 2}, pair{1, 2}, pair{1, 2}}},                               //
        {pair{1, 3}, {pair{0, 4}, pair{0, 5}, pair{0, 6}}},                               //
        {pair{-1, 3}, {pair{-1, 2}, pair{1, 3}, pair{4, 5}}},                             //
        {pair{1, 4}, {pair{1, 4}, pair{2, 3}, pair{0, 5}, pair{-2, 0}, pair{5, 7}}},      //
        {pair{-5, 5}, {pair{-8, 0}, pair{4, 4}, pair{10, 10}, pair{2, 11}, pair{4, 10}}}, //
        {pair{0, 5}, {pair{4, 12}}},                                                      //
        {pair{2, 9}, {pair{-2, 3}, pair{-4, -1}, pair{-3, 5}}},                           //
        {pair{2, 5}, {pair{2, 4}, pair{3, 7}, pair{1, 4}}},                               //
        {pair{-3, 2}, {pair{-1, 7}, pair{-2, 6}, pair{1, 8}, pair{4, 11}}},               //
        // Constant array entries: forced winner / fixed pivot.
        {pair{-5, 10}, {3, pair{0, 7}, 5}},                      //
        {pair{-5, 10}, {pair{0, 4}, 7, pair{1, 6}, pair{2, 9}}}, //
        // Degenerate cases (issue #254): all-constant arrays + genuine constant
        // result. Each row is run for both Min and Max; build_expected computes
        // the per-direction truth. (Empty array is rejected at construction by
        // ArrayMin/ArrayMax::prepare and so is covered separately, not here.)
        {4, {4, 4, 4}},                    // all equal: min == max == 4, result 4 (tautology both)
        {4, {3, 5, 4}},                    // min 3 / max 5: result 4 wrong for both (contradiction both)
        {4, {4}},                          // single constant element (tautology both)
        {3, {4}},                          // single constant element: result 3 wrong (contradiction both)
        {pair{0, 9}, {3, 5, pair{0, 9}}}}; // mixed: two constants plus a variable

    mt19937 rand(*get_seed());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 5);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_bounds(-5, 5, 3, 7), vector(n_values, random_bounds_or_constant(-5, 5, 3, 8)));
    }

    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 5);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_constant(-5, 5), vector(n_values, random_bounds_or_constant(-5, 5, 3, 8)));
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2] : data) {
            run_min_max_test(proofs, view_cfg, false, r1, r2);
            run_min_max_test(proofs, view_cfg, true, r1, r2);
        }
        if (run_dup) {
            for (bool m : {true, false}) {
                // {x, x, y} — duplicates in array.
                run_dup_min_max_test(proofs, m, "xxy", {{1, 5}, {1, 5}}, {0, 0, 1}, -1, {0, 6});
                // {x, y, x} — non-adjacent dup.
                run_dup_min_max_test(proofs, m, "xyx", {{1, 5}, {1, 5}}, {0, 1, 0}, -1, {0, 6});
                // {x, y} with result = x — Min: x <= y; Max: x >= y.
                run_dup_min_max_test(proofs, m, "xy_resx", {{1, 5}, {1, 5}}, {0, 1}, 0, {0, 6});
                // {x, y, z} with result = y — forces y == min/max(x,y,z).
                run_dup_min_max_test(proofs, m, "xyz_resy", {{1, 4}, {1, 4}, {1, 4}}, {0, 1, 2}, 1, {0, 5});
            }
        }
    }

    // Degenerate (issue #254): min/max over an empty array has no well-defined
    // value, and must be rejected with a clean exception rather than asserting
    // or reading past the end of the (empty) container.
    {
        bool empty_min_throws = false, empty_max_throws = false;
        try {
            Problem p;
            auto result = p.create_integer_variable(0_i, 5_i);
            p.post(ArrayMin{vector<IntegerVariableID>{}, result});
            solve(p, [](const CurrentState &) { return true; });
        }
        catch (const InvalidProblemDefinitionException &) {
            empty_min_throws = true;
        }
        try {
            Problem p;
            auto result = p.create_integer_variable(0_i, 5_i);
            p.post(ArrayMax{vector<IntegerVariableID>{}, result});
            solve(p, [](const CurrentState &) { return true; });
        }
        catch (const InvalidProblemDefinitionException &) {
            empty_max_throws = true;
        }
        if (! empty_min_throws || ! empty_max_throws) {
            println(cerr, "min/max over empty array: expected InvalidProblemDefinitionException");
            return EXIT_FAILURE;
        }
    }

    return EXIT_SUCCESS;
}
