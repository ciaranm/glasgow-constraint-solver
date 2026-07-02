#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/multiply.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>

#include <cstdlib>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif
#include <iostream>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

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

namespace
{
    auto level_name(const MultiplyConsistency & level) -> string
    {
        return overloaded{                                              //
            [](const consistency::Auto &) -> string { return "auto"; }, //
            [](const consistency::BC &) -> string { return "bc"; },     //
            [](const consistency::Tabulated &) -> string { return "tabulated"; }}
            .visit(level);
    }
}

// Three distinct variables, optionally through views: constrain
// (m1 * v1 + o1) * (m2 * v2 + o2) = (m3 * v3 + o3) and enumerate over the
// underlying variables. With all multipliers 1 and offsets 0 this is the plain
// case.
auto run_multiply_test(bool proofs, const MultiplyConsistency & level, bool check_gac, pair<int, int> v1_range, pair<int, int> v2_range,
    pair<int, int> v3_range, tuple<int, int, int, int, int, int> view_spec = {1, 0, 1, 0, 1, 0}) -> void
{
    const auto & [m1, o1, m2, o2, m3, o3] = view_spec;
    print(cerr, "multiply {} {} {} {} {} views {} {}", level_name(level), check_gac ? "gac-checked" : "plain", v1_range, v2_range, v3_range,
        view_spec, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    auto is_satisfying = [&](int a, int b, int c) { return (m1 * a + o1) * (m2 * b + o2) == (m3 * c + o3); };
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second), "v1");
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second), "v2");
    auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second), "v3");

    auto wrap = [&](SimpleIntegerVariableID v, int m, int o) -> IntegerVariableID {
        IntegerVariableID result = v;
        if (m == -1)
            result = -result;
        return result + Integer{o};
    };
    p.post(Multiply{wrap(v1, m1, o1), wrap(v2, m2, o2), wrap(v3, m3, o3), level});

    auto proof_name = proofs ? make_optional("multiply_test") : nullopt;

    if (check_gac)
        solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});
    else
        solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

// Aliased shapes: x * x = y, x * y = x, y * x = x, and x * x = x. These used
// to be only expressible through the table-based Times; MultiplyBC itself
// still throws on them, so Multiply decomposes.
auto run_alias_test(
    bool proofs, const MultiplyConsistency & level, bool check_gac, const string & shape, pair<int, int> x_range, pair<int, int> y_range) -> void
{
    print(cerr, "multiply {} {} alias {} {} {} {}", level_name(level), check_gac ? "gac-checked" : "plain", shape, x_range, y_range,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    Problem p;
    auto x = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second), "x");
    auto y = p.create_integer_variable(Integer(y_range.first), Integer(y_range.second), "y");

    set<tuple<int, int>> expected, actual;
    if (shape == "xxy") {
        build_expected(expected, [](int a, int b) { return a * a == b; }, x_range, y_range);
        p.post(Multiply{x, x, y, level});
    }
    else if (shape == "xyx") {
        build_expected(expected, [](int a, int b) { return a * b == a; }, x_range, y_range);
        p.post(Multiply{x, y, x, level});
    }
    else if (shape == "yxx") {
        build_expected(expected, [](int a, int b) { return b * a == a; }, x_range, y_range);
        p.post(Multiply{y, x, x, level});
    }
    else
        throw UnexpectedException{"unknown alias shape"};

    println(cerr, " expecting {} solutions", expected.size());

    auto proof_name = proofs ? make_optional("multiply_test") : nullopt;

    if (check_gac)
        solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{x, y});
    else
        solve_for_tests(p, proof_name, actual, tuple{x, y});

    check_results(proof_name, expected, actual);
}

// The x * x = x special case, one variable only.
auto run_all_same_test(bool proofs, const MultiplyConsistency & level, pair<int, int> x_range) -> void
{
    print(cerr, "multiply {} alias xxx {} {}", level_name(level), x_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    Problem p;
    auto x = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second), "x");
    p.post(Multiply{x, x, x, level});

    set<tuple<int>> expected, actual;
    build_expected(expected, [](int a) { return a * a == a; }, x_range);
    println(cerr, " expecting {} solutions", expected.size());

    auto proof_name = proofs ? make_optional("multiply_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x});
    check_results(proof_name, expected, actual);
}

// Constant operands: c * v = r, v * c = r, c1 * c2 = r, and a constant result
// v1 * v2 = c.
auto run_constant_test(
    bool proofs, const MultiplyConsistency & level, const string & shape, int constant, pair<int, int> v_range, pair<int, int> r_range) -> void
{
    print(cerr, "multiply {} constant {} c={} {} {} {}", level_name(level), shape, constant, v_range, r_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    Problem p;
    auto v = p.create_integer_variable(Integer(v_range.first), Integer(v_range.second), "v");
    auto r = p.create_integer_variable(Integer(r_range.first), Integer(r_range.second), "r");

    set<tuple<int, int>> expected, actual;
    if (shape == "cv") {
        build_expected(expected, [&](int a, int b) { return constant * a == b; }, v_range, r_range);
        p.post(Multiply{constant_variable(Integer{constant}), v, r, level});
    }
    else if (shape == "vc") {
        build_expected(expected, [&](int a, int b) { return a * constant == b; }, v_range, r_range);
        p.post(Multiply{v, constant_variable(Integer{constant}), r, level});
    }
    else if (shape == "result") {
        build_expected(expected, [&](int a, int b) { return a * b == constant; }, v_range, r_range);
        p.post(Multiply{v, r, constant_variable(Integer{constant}), level});
    }
    else
        throw UnexpectedException{"unknown constant shape"};

    println(cerr, " expecting {} solutions", expected.size());

    auto proof_name = proofs ? make_optional("multiply_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v, r});
    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<MultiplyConsistency> levels{consistency::Auto{}, consistency::BC{}, consistency::Tabulated{}};

    // Random instances for the forced-BC variant: domains big enough that Auto
    // would not tabulate, so this is the decomposition's bounds propagation.
    // Soundness and completeness are checked against a full enumeration;
    // per-node bounds consistency is deliberately not claimed (the composition
    // is weaker than bounds consistency on the product, and MultiplyBC's own
    // test notes the same).
    random_device rand_dev;
    mt19937 rand(rand_dev());
    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>>> random_bc_data;
    for (int x = 0; x < 4; ++x) {
        generate_random_data(rand, random_bc_data, random_bounds(-10, 10, 3, 12), random_bounds(-10, 10, 3, 12), random_bounds(-80, 80, 10, 60));
        generate_random_data(rand, random_bc_data, random_bounds(0, 20, 2, 8), random_bounds(-6, 6, 2, 8), random_bounds(-60, 60, 20, 80));
    }
    auto random_view_spec = [&]() -> tuple<int, int, int, int, int, int> {
        uniform_int_distribution<int> sign(0, 1), offset(-3, 3);
        return {sign(rand) ? 1 : -1, offset(rand), sign(rand) ? 1 : -1, offset(rand), sign(rand) ? 1 : -1, offset(rand)};
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        for (const auto & level : levels) {
            bool is_bc = holds_alternative<consistency::BC>(level);
            // Small domains: Auto tabulates (3 * 3 * 9 = 81 <= threshold) and GAC
            // is forced, so both are GAC; BC is checked for soundness only.
            run_multiply_test(proofs, level, ! is_bc, {1, 3}, {1, 3}, {1, 9});
            run_multiply_test(proofs, level, ! is_bc, {-2, 2}, {1, 2}, {-4, 4}, {1, 0, 1, 0, 1, 0});

            // Views, negatives, zero. 5 * 3 * 5 = 75 <= threshold.
            run_multiply_test(proofs, level, ! is_bc, {-2, 2}, {0, 2}, {-2, 2}, {1, 2, -1, 1, 1, -1});
            run_multiply_test(proofs, level, ! is_bc, {1, 3}, {1, 3}, {1, 5}, {-1, 0, 1, 0, -1, 2});

            // Aliased shapes, small: 7 * 10 = 70 and similar.
            run_alias_test(proofs, level, ! is_bc, "xxy", {-3, 3}, {0, 9});
            run_alias_test(proofs, level, ! is_bc, "xyx", {-2, 4}, {-3, 3});
            run_alias_test(proofs, level, ! is_bc, "yxx", {-3, 3}, {-2, 2});
            run_all_same_test(proofs, level, {-2, 2});

            // Constants fold to a linear equality.
            run_constant_test(proofs, level, "cv", 3, {-4, 4}, {-12, 12});
            run_constant_test(proofs, level, "vc", -2, {-4, 4}, {-8, 8});
            run_constant_test(proofs, level, "vc", 0, {-4, 4}, {-2, 2});
            run_constant_test(proofs, level, "result", 6, {-8, 8}, {-8, 8});
        }

        // Wider domains: Auto falls back on bounds consistency; soundness and
        // completeness are still checked, per-node consistency is not.
        run_multiply_test(proofs, consistency::Auto{}, false, {-10, 10}, {-10, 10}, {-100, 100});
        run_multiply_test(proofs, consistency::Auto{}, false, {2, 20}, {-8, 8}, {-160, 160}, {1, 0, 1, 1, 1, 0});
        run_alias_test(proofs, consistency::Auto{}, false, "xxy", {-12, 12}, {0, 144});
        run_constant_test(proofs, consistency::Auto{}, "cv", 7, {-30, 30}, {-210, 210});

        // Random instances, forced BC, with and without view wraps.
        for (const auto & [r1, r2, r3] : random_bc_data)
            run_multiply_test(proofs, consistency::BC{}, false, r1, r2, r3);
        for (std::size_t x = 0; x < 4; ++x) {
            const auto & [r1, r2, r3] = random_bc_data.at(x);
            run_multiply_test(proofs, consistency::BC{}, false, r1, r2, r3, random_view_spec());
        }
    }

    // A forced-GAC tabulation on a domain above the Auto threshold still works,
    // it is just more expensive.
    if (can_run_veripb())
        run_multiply_test(true, consistency::Tabulated{}, true, {-4, 4}, {-4, 4}, {-16, 16});

    return EXIT_SUCCESS;
}
