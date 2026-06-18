#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <vector>

#include <version>
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ranges.h>
#endif

using std::cerr;
using std::cout;
using std::flush;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::tuple;
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

auto check_lex(vector<Integer> & x_sols, vector<Integer> & y_sols, bool or_equal = false) -> bool
{
    if (x_sols.size() != y_sols.size()) cout << "Tuples not same length!";
    if (or_equal ? x_sols[0] >= y_sols[0] : x_sols[0] > y_sols[0]) return true;
    if (or_equal ? y_sols[0] >= x_sols[0] : y_sols[0] > x_sols[0]) return false;
    if (x_sols.size() == 1) return false;

    vector<Integer> x_sols_smaller = {x_sols.begin() + 1, x_sols.end()};
    vector<Integer> y_sols_smaller = {y_sols.begin() + 1, y_sols.end()};
    return check_lex(x_sols_smaller, y_sols_smaller);
}

auto check_at_most_1(vector<Integer> & x_sols, Integer value, bool at_least, bool in_set)
{
    auto count = 0;
    for (const auto & x_val : x_sols) {

        if (in_set) {
            (x_val == 1_i || x_val == value) && count++;
        }
        else {
            (x_val == value) && count++;
        }
    }

    return at_least ? count >= 1 : count <= 1;
}

auto run_lex_test(bool proofs, const string & mode, int length, vector<pair<int, int>> ranges, bool reverse = false, bool or_equal = false, bool fixed_y = false) -> bool
{
    auto proof_basename = "smart_table_test_" + mode;
    vector<IntegerVariableID> x;
    vector<IntegerVariableID> y;
    vector<Integer> fixed_y_vals;
    Problem p;

    for (int i = 0; i < length; i++) {
        x.emplace_back(p.create_integer_variable(Integer(ranges[i].first), Integer(ranges[i].second)));
        if (! fixed_y)
            y.emplace_back(p.create_integer_variable(Integer(ranges[i].first), Integer(ranges[i].second)));
        else
            fixed_y_vals.emplace_back(Integer{i});
    }
    SmartTuples tuples;

    for (int i = 0; i < length; ++i) {
        vector<SmartEntry> tuple;
        for (int j = 0; j < i + 1; ++j) {
            if (! fixed_y) {
                if (j < i) {
                    tuple.emplace_back(SmartTable::equals(x[j], y[j]));
                }
                else if (j == i) {
                    if (reverse) {
                        if (or_equal)
                            tuple.emplace_back(SmartTable::less_than_equal(x[j], y[j]));
                        else
                            tuple.emplace_back(SmartTable::less_than(x[j], y[j]));
                    }
                    else {
                        if (or_equal)
                            tuple.emplace_back(SmartTable::greater_than_equal(x[j], y[j]));
                        else
                            tuple.emplace_back(SmartTable::greater_than(x[j], y[j]));
                    }
                }
            }
            else {
                if (j < i) {
                    tuple.emplace_back(SmartTable::equals(x[j], fixed_y_vals[j]));
                }
                else if (j == i) {
                    if (reverse) {
                        if (or_equal)
                            tuple.emplace_back(SmartTable::less_than_equal(x[j], fixed_y_vals[j]));
                        else
                            tuple.emplace_back(SmartTable::less_than(x[j], fixed_y_vals[j]));
                    }
                    else {
                        if (or_equal)
                            tuple.emplace_back(SmartTable::greater_than_equal(x[j], fixed_y_vals[j]));
                        else
                            tuple.emplace_back(SmartTable::greater_than(x[j], fixed_y_vals[j]));
                    }
                }
            }
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = x;
    if (! fixed_y) all_vars.insert(all_vars.end(), y.begin(), y.end());

    p.post(SmartTable{all_vars, tuples});

    bool lex_violated = false;
    optional<ProofOptions> proof_options = proofs ? make_optional(ProofOptions{proof_basename}) : nullopt;
    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                vector<Integer> x_sols;
                vector<Integer> y_sols;
                for (int i = 0; i < length; ++i) {
                    x_sols.emplace_back(s(x[i]));
                    y_sols.emplace_back(fixed_y ? fixed_y_vals[i] : s(y[i]));
                }
                lex_violated = lex_violated || (reverse ? (! check_lex(y_sols, x_sols, or_equal)) : (! check_lex(x_sols, y_sols, or_equal)));
                return true;
            }},
        proof_options);

    if (lex_violated)
        return false;
    return ! proofs || run_veripb(proof_basename + ".opb", proof_basename + ".pbp");
}

auto run_at_most_1_test(bool proofs, const string & mode, int length, vector<pair<int, int>> & ranges, bool at_least, bool in_set) -> bool
{
    auto proof_basename = "smart_table_test_" + mode;
    vector<IntegerVariableID> x;
    Problem p;

    for (int i = 0; i < length; i++) {
        x.emplace_back(p.create_integer_variable(Integer(ranges[i].first), Integer(ranges[i].second)));
    }
    auto y = p.create_integer_variable(Integer{length}, Integer{length}, "y");

    SmartTuples tuples;

    for (int i = 0; i < length; ++i) {
        vector<SmartEntry> tuple;
        for (int j = 0; j < length; ++j) {
            if (j != i) {
                if (at_least) {
                    if (in_set) {
                        tuple.emplace_back(SmartTable::in_set(x[j], {1_i, Integer{length}}));
                    }
                    else {
                        tuple.emplace_back(SmartTable::equals(x[j], y));
                    }
                }
                else {
                    if (in_set) {
                        tuple.emplace_back(SmartTable::not_in_set(x[j], {1_i, Integer{length}}));
                    }
                    else {
                        tuple.emplace_back(SmartTable::not_equals(x[j], y));
                    }
                }
            }
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = x;
    all_vars.emplace_back(y);

    p.post(SmartTable{all_vars, tuples});
    bool at_most_1_violated = false;

    optional<ProofOptions> proof_options = proofs ? make_optional(ProofOptions{proof_basename}) : nullopt;
    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                vector<Integer> x_sols;
                for (int i = 0; i < length; ++i)
                    x_sols.emplace_back(s(x[i]));
                at_most_1_violated = at_most_1_violated || ! check_at_most_1(x_sols, Integer{length}, at_least, in_set);
                return true;
            }},
        proof_options);

    if (at_most_1_violated)
        return false;
    return ! proofs || run_veripb(proof_basename + ".opb", proof_basename + ".pbp");
}

// One tuple using the same variable in several entries at once, mixing
// binary and unary SmartEntries: y appears in a not-equals, an in-set, and
// a greater-than. The PB encoding must combine the per-entry supports for
// y rather than treating each entry independently.
auto run_mixed_same_var_test(bool proofs, const string & mode) -> void
{
    auto proof_basename = "smart_table_test_" + mode;
    for (const auto & [lower, upper] : vector<pair<int, int>>{{-1, 3}, {-2, 2}, {0, 4}}) {
        print(cerr, "smart table {} over {}..{}{}", mode, lower, upper, proofs ? " with proofs:" : ":");
        cerr << flush;
        set<tuple<int, int, int>> expected, actual;

        build_expected(
            expected, [&](int x, int y, int z) {
                return y != x && (y == -1 || y == 2 || y == 3) && (z == -1 || z == 0 || z == 1) && z > y;
            },
            pair{lower, upper}, pair{lower, upper}, pair{lower, upper});
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto x = p.create_integer_variable(Integer{lower}, Integer{upper}, "x");
        auto y = p.create_integer_variable(Integer{lower}, Integer{upper}, "y");
        auto z = p.create_integer_variable(Integer{lower}, Integer{upper}, "z");
        auto tuples = SmartTuples{{SmartTable::not_equals(y, x), SmartTable::in_set(y, {-1_i, 2_i, 3_i}),
            SmartTable::in_set(z, {-1_i, 0_i, 1_i}), SmartTable::greater_than(z, y)}};
        p.post(SmartTable{{x, y, z}, tuples});

        auto proof_name = proofs ? make_optional(proof_basename) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x, y, z});
        check_results(proof_name, expected, actual);
    }
}

// Several unary entries restricting the same variable inside one tuple
// must be consolidated into a single restriction in the PB encoding, or
// unsupported values fail to unit propagate. The first instance is an
// originally-failing case found by random testing (issue #40, from
// random_smart_table seed 792395939); it has no solutions. The second
// mixes stacked unary entries with binary entries and has solutions.
auto run_stacked_unary_test(bool proofs, const string & mode) -> void
{
    auto proof_basename = "smart_table_test_" + mode;
    {
        print(cerr, "smart table {} unsat instance{}", mode, proofs ? " with proofs:" : ":");
        cerr << flush;
        set<tuple<int, int, int, int>> expected, actual;

        build_expected(
            expected, [&](int x0, int x1, int x2, int x3) {
                bool t1 = x2 < 1 && x3 != 1 && x1 > 0 && x0 == 1 &&
                    (x3 == 3 || x3 == 1 || x3 == 2 || x3 == -1) && x2 != 2 && x2 != 0 && x1 > 1 && x2 == 0;
                bool t2 = x3 >= 1 && (x2 == 0 || x2 == 3 || x2 == 1) && (x3 == 4 || x3 == 1) && x3 == 2;
                bool t3 = x1 == x0 && x3 <= 2 && x2 < 3 && x3 < 0 &&
                    (x1 == 3 || x1 == -1 || x1 == 2) && x1 > 3 && x0 != 0 && x0 != 1;
                return t1 || t2 || t3;
            },
            pair{-1, 4}, pair{-1, 4}, pair{-1, 4}, pair{-1, 4});
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto x = p.create_integer_variable_vector(4, -1_i, 4_i, "x");
        auto tuples = SmartTuples{
            {SmartTable::less_than(x[2], 1_i), SmartTable::not_equals(x[3], 1_i), SmartTable::greater_than(x[1], 0_i), SmartTable::equals(x[0], 1_i),
                SmartTable::in_set(x[3], {3_i, 1_i, 2_i, -1_i}), SmartTable::not_in_set(x[2], {2_i, 0_i}), SmartTable::greater_than(x[1], 1_i), SmartTable::equals(x[2], 0_i)},
            {SmartTable::greater_than_equal(x[3], 1_i), SmartTable::in_set(x[2], {0_i, 3_i, 1_i}), SmartTable::in_set(x[3], {4_i, 1_i}), SmartTable::equals(x[3], 2_i)},
            {SmartTable::equals(x[1], x[0]), SmartTable::less_than_equal(x[3], 2_i), SmartTable::less_than(x[2], 3_i), SmartTable::less_than(x[3], 0_i),
                SmartTable::in_set(x[1], {3_i, -1_i, 2_i}), SmartTable::greater_than(x[1], 3_i), SmartTable::not_in_set(x[0], {0_i, 1_i})}};
        p.post(SmartTable{x, tuples});

        auto proof_name = proofs ? make_optional(proof_basename) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x[0], x[1], x[2], x[3]});
        check_results(proof_name, expected, actual);
    }
    {
        print(cerr, "smart table {} sat instance{}", mode, proofs ? " with proofs:" : ":");
        cerr << flush;
        set<tuple<int, int>> expected, actual;

        build_expected(
            expected, [&](int a, int b) {
                bool t1 = a < 3 && a != 1 && a != 0 && b >= a;
                bool t2 = a >= 3 && (b == 4 || b == 1) && b != 4;
                return t1 || t2;
            },
            pair{-1, 4}, pair{-1, 4});
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto a = p.create_integer_variable(-1_i, 4_i, "a");
        auto b = p.create_integer_variable(-1_i, 4_i, "b");
        auto tuples = SmartTuples{
            {SmartTable::less_than(a, 3_i), SmartTable::not_equals(a, 1_i), SmartTable::not_in_set(a, {0_i}), SmartTable::greater_than_equal(b, a)},
            {SmartTable::greater_than_equal(a, 3_i), SmartTable::in_set(b, {4_i, 1_i}), SmartTable::not_equals(b, 4_i)}};
        p.post(SmartTable{{a, b}, tuples});

        auto proof_name = proofs ? make_optional(proof_basename) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{a, b});
        check_results(proof_name, expected, actual);
    }
}

// Unary constant comparisons combined with a variable-variable binary
// entry over wide, negative-heavy bounds, with the constant at the lower
// bound, the upper bound, and mid-range of its variable. The largest
// instance exceeds the default solution cap, so completeness on it is
// only checked in caps-off builds; the others stay under the cap.
auto run_wide_constants_test(bool proofs, const string & mode) -> void
{
    auto proof_basename = "smart_table_test_" + mode;
    struct Instance
    {
        pair<int, int> x_range;
        pair<int, int> y_range;
        int c;
    };
    for (const auto & [x_range, y_range, c] : vector<Instance>{
             {{-59, 58}, {-18, 17}, -18},
             {{-59, 58}, {-18, 17}, 17},
             {{-15, 14}, {-9, 8}, -9}}) {
        print(cerr, "smart table {} x in {}, y in {}, y >= {}{}", mode, x_range, y_range, c, proofs ? " with proofs:" : ":");
        cerr << flush;
        set<tuple<int, int>> expected, actual;

        build_expected(
            expected, [&](int x, int y) { return y >= c && x > y; }, x_range, y_range);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto x = p.create_integer_variable(Integer{x_range.first}, Integer{x_range.second}, "x");
        auto y = p.create_integer_variable(Integer{y_range.first}, Integer{y_range.second}, "y");
        auto tuples = SmartTuples{{SmartTable::greater_than_equal(y, Integer{c}), SmartTable::greater_than(x, y)}};
        p.post(SmartTable{{x, y}, tuples});

        auto proof_name = proofs ? make_optional(proof_basename) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x, y});
        check_results(proof_name, expected, actual);
    }
}

// issue #254: degenerate SmartTable instances — an empty tuple list (no
// allowed tuple, so unsatisfiable), all-fixed (singleton-domain) variables in
// both the matching and non-matching directions, and a single-variable table.
auto run_degenerate_test(bool proofs, const string & mode) -> void
{
    auto basename = "smart_table_test_" + mode;

    // Empty tuple list: unsatisfiable.
    {
        print(cerr, "smart table {} empty-tuples{}", mode, proofs ? " with proofs:" : ":");
        cerr << flush;
        Problem p;
        auto x = p.create_integer_variable(1_i, 2_i);
        auto y = p.create_integer_variable(1_i, 2_i);
        p.post(SmartTable{{x, y}, SmartTuples{}});
        set<tuple<int, int>> expected, actual; // empty: unsatisfiable
        auto proof_name = proofs ? make_optional(basename + "_empty") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x, y});
        check_results(proof_name, expected, actual);
    }

    // All-fixed variables that satisfy the (single) tuple.
    {
        print(cerr, "smart table {} fixed-match{}", mode, proofs ? " with proofs:" : ":");
        cerr << flush;
        Problem p;
        auto x = p.create_integer_variable(1_i, 1_i);
        auto y = p.create_integer_variable(2_i, 2_i);
        p.post(SmartTable{{x, y}, SmartTuples{{SmartTable::equals(x, 1_i), SmartTable::equals(y, 2_i)}}});
        set<tuple<int, int>> expected{{1, 2}}, actual;
        auto proof_name = proofs ? make_optional(basename + "_match") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x, y});
        check_results(proof_name, expected, actual);
    }

    // All-fixed variables that violate the tuple: unsatisfiable.
    {
        print(cerr, "smart table {} fixed-nomatch{}", mode, proofs ? " with proofs:" : ":");
        cerr << flush;
        Problem p;
        auto x = p.create_integer_variable(1_i, 1_i);
        auto y = p.create_integer_variable(3_i, 3_i);
        p.post(SmartTable{{x, y}, SmartTuples{{SmartTable::equals(x, 1_i), SmartTable::equals(y, 2_i)}}});
        set<tuple<int, int>> expected, actual; // empty: y is fixed to 3, tuple needs y == 2
        auto proof_name = proofs ? make_optional(basename + "_nomatch") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x, y});
        check_results(proof_name, expected, actual);
    }

    // Single variable, single unary tuple selecting a subset of the domain.
    {
        print(cerr, "smart table {} single-var{}", mode, proofs ? " with proofs:" : ":");
        cerr << flush;
        Problem p;
        auto x = p.create_integer_variable(1_i, 3_i);
        p.post(SmartTable{{x}, SmartTuples{{SmartTable::equals(x, 2_i)}}});
        set<tuple<int>> expected{{2}}, actual;
        auto proof_name = proofs ? make_optional(basename + "_single") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x});
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    if (argc != 2)
        throw UnimplementedException{};

    vector<pair<int, vector<pair<int, int>>>> data = {
        // Length    //Ranges
        {3, {{1, 3}, {1, 2}, {2, 3}}},
        {3, {{1, 2}, {1, 2}, {1, 2}}},
        {4, {{-3, 0}, {1, 4}, {3, 3}, {3, 3}}},
        {4, {{5, 5}, {2, 4}, {0, 4}, {1, 5}}},
        {5, {{-1, 4}, {3, 6}, {2, 2}, {3, 3}, {3, 5}}},
        {5, {{1, 1}, {2, 2}, {3, 3}, {4, 4}, {1, 10}}}};

    string mode{argv[1]};

    // These modes carry their own instances rather than using the
    // length/ranges table below.
    if (mode == "mixed_same_var" || mode == "stacked_unary" || mode == "wide_constants" || mode == "degenerate") {
        for (bool proofs : {false, true}) {
            if (proofs && ! can_run_veripb())
                continue;
            if (mode == "mixed_same_var")
                run_mixed_same_var_test(proofs, mode);
            else if (mode == "stacked_unary")
                run_stacked_unary_test(proofs, mode);
            else if (mode == "wide_constants")
                run_wide_constants_test(proofs, mode);
            else
                run_degenerate_test(proofs, mode);
        }
        return EXIT_SUCCESS;
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [length, ranges] : data) {
            if (mode == "lex_gt") {
                // x > y
                if (! run_lex_test(proofs, mode, length, ranges, false, false, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_ge") {
                // x >= y
                if (! run_lex_test(proofs, mode, length, ranges, false, true, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_lt") {
                // x < y
                if (! run_lex_test(proofs, mode, length, ranges, true, false, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_le") {
                // x <= y
                if (! run_lex_test(proofs, mode, length, ranges, true, true, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_gt_fixed") {
                // x > [1,..,n]
                if (! run_lex_test(proofs, mode, length, ranges, false, false, true))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_ge_fixed") {
                // x >= [1,..,n]
                if (! run_lex_test(proofs, mode, length, ranges, false, true, true))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_lt_fixed") {
                // x < [1,..,n]
                if (! run_lex_test(proofs, mode, length, ranges, true, false, true))
                    return EXIT_FAILURE;
            }
            else if (mode == "lex_le_fixed") {
                // x <= [1,..,n]
                if (! run_lex_test(proofs, mode, length, ranges, true, true, true))
                    return EXIT_FAILURE;
            }
            else if (mode == "am1_eq") {
                // at most one var in x == length
                if (! run_at_most_1_test(proofs, mode, length, ranges, false, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "am1_in_set") {
                // at most one var in x one of {1, length}
                if (! run_at_most_1_test(proofs, mode, length, ranges, false, true))
                    return EXIT_FAILURE;
            }
            else if (mode == "al1_eq") {
                // at least one var in x == length
                if (! run_at_most_1_test(proofs, mode, length, ranges, true, false))
                    return EXIT_FAILURE;
            }
            else if (mode == "al1_in_set") {
                // at least one var in x one of {1, length}
                if (! run_at_most_1_test(proofs, mode, length, ranges, true, true))
                    return EXIT_FAILURE;
            }
            else
                throw UnimplementedException{};
        }
    }

    return EXIT_SUCCESS;
}
