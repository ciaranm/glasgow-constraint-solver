#include <gcs/constraints/element.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
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
using std::cmp_less;
using std::flush;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::tuple;
using std::uniform_int_distribution;
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

auto run_element_test(bool proofs, const string & mode, const ViewWrapConfig & view_cfg, pair<int, int> var_range, pair<int, int> idx_range,
    const vector<pair<int, int>> & array_range) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2 + static_cast<int>(array_range.size()));
    print(cerr, "element [{}] {} {} {} {}", view_wrap_config_label(view_cfg), var_range, idx_range, array_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, vector<int>>> expected, actual;
    build_expected(
        expected, [&](int v, int x, const vector<int> & a) { return x >= 0 && cmp_less(x, a.size()) && a.at(x) == v; }, var_range, idx_range,
        array_range);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = create_integer_variable_or_constant_with_view(p, var_range, wraps.at(0));
    auto idx = create_integer_variable_or_constant_with_view(p, idx_range, wraps.at(1));
    vector<IntegerVariableID> array;
    for (const auto & r : array_range)
        array.push_back(create_integer_variable_or_constant_with_view(p, r, wraps.at(array.size() + 2)));
    // GAC is Element's default; setting it explicitly drives the with_consistency
    // setter end-to-end while keeping the checking_gac assertion valid.
    p.post(Element{var, idx, &array}.with_consistency(consistency::GAC{}));

    auto proof_name = proofs ? make_optional("element_test_" + mode + "_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{var, idx, array});

    check_results(proof_name, expected, actual);
}

auto run_element_constant_test(bool proofs, const string & mode, const ViewWrapConfig & view_cfg, pair<int, int> var_range, pair<int, int> idx_range,
    const vector<int> & array) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2);
    print(cerr, "element constant [{}] {} {} {} {}", view_wrap_config_label(view_cfg), var_range, idx_range, array, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int>> expected, actual;
    build_expected(expected, [&](int v, int x) { return x >= 0 && cmp_less(x, array.size()) && array.at(x) == v; }, var_range, idx_range);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = create_integer_variable_or_constant_with_view(p, var_range, wraps.at(0));
    auto idx = create_integer_variable_or_constant_with_view(p, idx_range, wraps.at(1));
    vector<Integer> a;
    for (const auto & v : array)
        a.push_back(Integer(v));
    p.post(ElementConstantArray{var, idx, &a});

    auto proof_name = proofs ? make_optional("element_test_" + mode + "_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{var, CheckConsistency::BC}, pair{idx, CheckConsistency::GAC}});

    check_results(proof_name, expected, actual);
}

auto run_element2d_test(bool proofs, const string & mode, const ViewWrapConfig & view_cfg, pair<int, int> var_range, pair<int, int> idx1_range,
    pair<int, int> idx2_range, const vector<vector<pair<int, int>>> & array_range) -> void
{
    int n_array = 0;
    for (const auto & row : array_range)
        n_array += static_cast<int>(row.size());
    auto wraps = wraps_for_positions(view_cfg, 3 + n_array);
    print(cerr, "element2d [{}] {} {} {} {} {}", view_wrap_config_label(view_cfg), var_range, idx1_range, idx2_range, array_range,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int, vector<vector<int>>>> expected, actual;
    build_expected(
        expected,
        [&](int v, int x, int y, const vector<vector<int>> & a) {
            return x >= 0 && cmp_less(x, a.size()) && y >= 0 && cmp_less(y, a.at(0).size()) && a.at(x).at(y) == v;
        },
        var_range, idx1_range, idx2_range, array_range);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = create_integer_variable_or_constant_with_view(p, var_range, wraps.at(0));
    auto idx1 = create_integer_variable_or_constant_with_view(p, idx1_range, wraps.at(1));
    auto idx2 = create_integer_variable_or_constant_with_view(p, idx2_range, wraps.at(2));
    vector<vector<IntegerVariableID>> a;
    std::size_t pos = 3;
    for (const auto & v : array_range) {
        a.emplace_back();
        for (const auto & r : v)
            a.back().push_back(create_integer_variable_or_constant_with_view(p, r, wraps.at(pos++)));
    }
    p.post(Element2D{var, idx1, idx2, &a});

    auto proof_name = proofs ? make_optional("element_test_" + mode + "_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{var, idx1, idx2, a});

    check_results(proof_name, expected, actual);
}

auto run_element2d_constant_test(bool proofs, const string & mode, const ViewWrapConfig & view_cfg, pair<int, int> var_range,
    pair<int, int> idx1_range, pair<int, int> idx2_range, const vector<vector<int>> & array) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 3);
    print(cerr, "element 2d constant [{}] {} {} {} {} {}", view_wrap_config_label(view_cfg), var_range, idx1_range, idx2_range, array,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int>> expected, actual;
    build_expected(
        expected,
        [&](int v, int x, int y) {
            return x >= 0 && cmp_less(x, array.size()) && y >= 0 && cmp_less(y, array.at(0).size()) && array.at(x).at(y) == v;
        },
        var_range, idx1_range, idx2_range);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = create_integer_variable_or_constant_with_view(p, var_range, wraps.at(0));
    auto idx1 = create_integer_variable_or_constant_with_view(p, idx1_range, wraps.at(1));
    auto idx2 = create_integer_variable_or_constant_with_view(p, idx2_range, wraps.at(2));
    vector<vector<Integer>> a;
    for (const auto & v : array) {
        a.emplace_back();
        for (const auto & vv : v)
            a.back().push_back(Integer(vv));
    }
    p.post(Element2DConstantArray{var, idx1, idx2, &a});

    auto proof_name = proofs ? make_optional("element_test_" + mode + "_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual,
        tuple{pair{var, CheckConsistency::BC}, pair{idx1, CheckConsistency::GAC}, pair{idx2, CheckConsistency::GAC}});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: Element with the same handle in several array
// positions, or the result var aliasing an array entry. Consistency
// isn't checked on dup runs; see tmp/duplicate_var_audit.md.
auto run_dup_element_test(bool proofs, const string & label, const vector<pair<int, int>> & unique_array_domains, const vector<int> & array_positions,
    pair<int, int> idx_range, int result_position_in_unique) -> void
{
    // result_position_in_unique == -1 means: create result as a fresh
    // variable. Otherwise the result variable IS unique_vars[result_position_in_unique].
    print(cerr, "element dup {} unique_doms={} positions={} idx={} result_pos={}{}", label, unique_array_domains, array_positions, idx_range,
        result_position_in_unique, proofs ? " with proofs:" : ":");
    cerr << flush;

    // Expected: pick values for each unique var, then evaluate the array
    // by indexing through array_positions and check Element semantics.
    set<tuple<vector<int>, int, int>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & unique_vals, int idx_val, int result_val) -> bool {
            if (idx_val < 0 || cmp_less(static_cast<int>(array_positions.size()), idx_val + 1))
                return false;
            int chosen = unique_vals.at(array_positions.at(idx_val));
            if (result_val != chosen)
                return false;
            if (result_position_in_unique >= 0)
                return unique_vals.at(result_position_in_unique) == result_val;
            return true;
        },
        unique_array_domains, idx_range, pair{-10, 10});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_array_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> array;
    for (auto pos : array_positions)
        array.push_back(unique_vars.at(pos));
    auto idx = p.create_integer_variable(Integer(idx_range.first), Integer(idx_range.second), "idx");
    IntegerVariableID var =
        (result_position_in_unique >= 0) ? unique_vars.at(result_position_in_unique) : p.create_integer_variable(Integer{-10}, Integer{10}, "var");
    p.post(Element{var, idx, &array});

    auto proof_name = proofs ? make_optional("element_test_dup_" + label) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars, idx, var});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    if (argc < 2)
        throw UnimplementedException{};

    string mode{argv[1]};
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Position layout per mode: var, then the index variable(s), then the
    // array entries (only when the array is itself made of variables). The
    // skip bound matches the registered n_positions for each mode.
    int n_positions = (mode == "const") ? 2 : (mode == "const2d") ? 3 : (mode == "var2d") ? 5 : 6;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "element view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }
    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    vector<tuple<pair<int, int>, pair<int, int>, vector<pair<int, int>>>> var_data = {{{1, 2}, {0, 1}, {{1, 2}, {1, 2}}}, //
        {{1, 2}, {-2, 2}, {{1, 2}, {1, 2}}},                                                                              //
        {{1, 2}, {0, 1}, {{1, 2}, {1, 2}, {1, 2}}},                                                                       //
        {{-1, 3}, {0, 2}, {{-1, 2}, {1, 3}, {4, 5}}},                                                                     //
        {{1, 4}, {0, 4}, {{1, 4}, {2, 3}, {0, 5}, {-2, 0}, {5, 7}}},                                                      //
        {{-5, 5}, {-3, 2}, {{-8, 0}, {4, 4}, {10, 10}, {2, 11}, {4, 10}}},                                                //
        {{7, 10}, {0, 9}, {{8, 18}, {9, 19}, {-1, 0}, {-6, 0}}},                                                          //
        // Degenerate cases (issue #254): empty array (no valid index), and
        // all-fixed index/var/array in both directions including out-of-range.
        {{1, 2}, {0, 1}, {}},        // empty array: no valid index (unsat)
        {{1, 1}, {0, 0}, {{1, 1}}},  // all fixed, array[0]==1==var (tautology)
        {{2, 2}, {0, 0}, {{1, 1}}},  // all fixed, array[0]==1 != var 2 (contradiction)
        {{1, 1}, {1, 1}, {{1, 1}}}}; // all fixed, index 1 out of range (contradiction)

    vector<tuple<pair<int, int>, pair<int, int>, vector<int>>> const_data = {{{1, 2}, {1, 2}, {1, 2}}, //
        {{1, 2}, {0, 1}, {1, 2}},                                                                      //
        {{1, 2}, {0, 2}, {1, 2, 2}},                                                                   //
        {{1, 2}, {0, 2}, {1, 2, 5}},                                                                   //
        {{-4, 6}, {-3, 3}, {-7, 2, -4, -10}},                                                          //
        // Degenerate cases (issue #254): empty constant array + all-fixed.
        {{1, 2}, {0, 1}, {}},   // empty constant array: no valid index (unsat)
        {{4, 4}, {0, 0}, {4}},  // all fixed, array[0]==4==var (tautology)
        {{3, 3}, {0, 0}, {4}},  // all fixed, array[0]==4 != var 3 (contradiction)
        {{1, 1}, {1, 1}, {4}},  // all fixed, index 1 out of range (contradiction)
        {{3, 5}, {0, 0}, {4}}}; // var in 3..5 forced to array[0]==4 (single solution)

    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>, vector<vector<int>>>> const2d_data = {{{1, 2}, {1, 2}, {1, 2}, {{1, 2}, {1, 2}}}, //
        {{1, 2}, {0, 1}, {1, 2}, {{1, 2}, {1, 2}}},                                                                                                //
        {{1, 8}, {0, 3}, {0, 3}, {{1, 5}, {7, 9}, {3, 6}}},                                                                                        //
        // Degenerate (issue #254): empty 2D array (no rows) — no valid index.
        {{1, 2}, {0, 1}, {0, 1}, {}}, //
        // All-fixed 2D, both directions.
        {{5, 5}, {0, 0}, {0, 0}, {{5}}},  // a[0][0]==5==var (tautology)
        {{4, 4}, {0, 0}, {0, 0}, {{5}}}}; // a[0][0]==5 != var 4 (contradiction)

    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>, vector<vector<pair<int, int>>>>> var2d_data = {
        {{1, 2}, {1, 2}, {1, 2}, {{{1, 2}, {2, 3}}, {{1, 2}, {2, 3}}}},                       //
        {{2, 6}, {0, 2}, {0, 1}, {{{2, 4}, {0, 1}}, {{-2, -2}, {1, 3}}, {{-2, 1}, {-3, 0}}}}, //
        // Degenerate (issue #254): empty 2D array (no rows) — no valid index.
        {{1, 2}, {0, 1}, {0, 1}, {}}, //
        // All-fixed 2D.
        {{5, 5}, {0, 0}, {0, 0}, {{{5, 5}}}},  // a[0][0]==5==var (tautology)
        {{4, 4}, {0, 0}, {0, 0}, {{{5, 5}}}}}; // a[0][0]==5 != var 4 (contradiction)
    random_device rand_dev;
    mt19937 rand(rand_dev());

    uniform_int_distribution n_values_dist(1, 4);
    uniform_int_distribution larger_n_values_dist(1, 8);
    uniform_int_distribution smaller_n_values_dist(1, 3);

    for (int x = 0; x < 10; ++x) {
        auto n_values = n_values_dist(rand);
        generate_random_data(
            rand, var_data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 0, 10), vector{size_t(n_values), random_bounds(-5, 5, 3, 8)});
    }

    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution values_dist(-10, 10);
        auto n_values = larger_n_values_dist(rand);
        generate_random_data(rand, const_data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 0, 10), vector{size_t(n_values), values_dist});
    }

    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution values_dist(-10, 10);
        auto n_values_1 = larger_n_values_dist(rand);
        auto n_values_2 = larger_n_values_dist(rand);
        generate_random_data(rand, const2d_data, random_bounds(-10, 10, 5, 15), random_bounds(-2, 5, 0, 5), random_bounds(-2, 5, 0, 5),
            vector{size_t(n_values_1), vector{size_t(n_values_2), values_dist}});
    }

    for (int x = 0; x < 10; ++x) {
        auto n_values_1 = smaller_n_values_dist(rand);
        auto n_values_2 = smaller_n_values_dist(rand);
        generate_random_data(rand, var2d_data, random_bounds(-5, 5, 1, 5), random_bounds(-1, 1, 0, 3), random_bounds(-1, 1, 0, 3),
            vector{size_t(n_values_1), vector{size_t(n_values_2), random_bounds(-3, 3, 0, 3)}});
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        if (mode == "var") {
            for (auto & [r1, r2, r3] : var_data)
                run_element_test(proofs, mode, view_cfg, r1, r2, r3);

            if (run_dup) {
                // Dup-variable cases.
                // [x, y, x] — same handle at non-adjacent positions.
                run_dup_element_test(proofs, "xyx", {{1, 3}, {1, 3}}, {0, 1, 0}, {0, 2}, -1);
                // [x, x] — same handle at adjacent positions.
                run_dup_element_test(proofs, "xx", {{1, 3}}, {0, 0}, {0, 1}, -1);
                // [x, y, x] but result is x — forces idx-selected value = x.
                run_dup_element_test(proofs, "xyx_resx", {{1, 3}, {1, 3}}, {0, 1, 0}, {0, 2}, 0);
                // [x, y] with result = x — forces array[idx] = x, i.e. either
                // idx=0 (trivial) or idx=1 and y = x.
                run_dup_element_test(proofs, "xy_resx", {{1, 3}, {1, 3}}, {0, 1}, {0, 1}, 0);
            }
        }
        else if (mode == "const") {
            for (auto & [r1, r2, r3] : const_data)
                run_element_constant_test(proofs, mode, view_cfg, r1, r2, r3);
        }
        else if (mode == "const2d") {
            for (auto & [r1, r2, r3, r4] : const2d_data)
                run_element2d_constant_test(proofs, mode, view_cfg, r1, r2, r3, r4);
        }
        else if (mode == "var2d") {
            for (auto & [r1, r2, r3, r4] : var2d_data)
                run_element2d_test(proofs, mode, view_cfg, r1, r2, r3, r4);
        }
        else
            throw UnimplementedException{};
    }

    return EXIT_SUCCESS;
}
