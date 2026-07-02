#include <gcs/constraints/divide.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/modulus.hh>
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
    auto div_ok(int a, int b, int c) -> bool
    {
        return 0 != b && a / b == c;
    }

    auto mod_ok(int a, int b, int c) -> bool
    {
        return 0 != b && a % b == c;
    }

    auto level_name(const DivideConsistency & level) -> string
    {
        return overloaded{                                              //
            [](const consistency::Auto &) -> string { return "auto"; }, //
            [](const consistency::BC &) -> string { return "bc"; },     //
            [](const consistency::Tabulated &) -> string { return "tabulated"; }}
            .visit(level);
    }

    auto post_divmod(Problem & p, bool is_div, IntegerVariableID x, IntegerVariableID y, IntegerVariableID out, const DivideConsistency & level)
        -> void
    {
        if (is_div)
            p.post(Divide{x, y, out, level});
        else
            p.post(Modulus{x, y, out, level});
    }
}

// Three distinct variables, optionally through views: constrain
// (m1 * x + o1) op (m2 * y + o2) = (m3 * out + o3), enumerating over the
// underlying variables.
auto run_divmod_test(bool proofs, bool is_div, const DivideConsistency & level, bool check_gac, pair<int, int> x_range, pair<int, int> y_range,
    pair<int, int> out_range, tuple<int, int, int, int, int, int> view_spec = {1, 0, 1, 0, 1, 0}) -> void
{
    const auto & [m1, o1, m2, o2, m3, o3] = view_spec;
    print(cerr, "{} {} {} {} {} {} views {} {}", is_div ? "divide" : "modulus", level_name(level), check_gac ? "gac-checked" : "plain", x_range,
        y_range, out_range, view_spec, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    auto is_satisfying = [&](int a, int b, int c) {
        return is_div ? div_ok(m1 * a + o1, m2 * b + o2, m3 * c + o3) : mod_ok(m1 * a + o1, m2 * b + o2, m3 * c + o3);
    };
    build_expected(expected, is_satisfying, x_range, y_range, out_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second), "x");
    auto y = p.create_integer_variable(Integer(y_range.first), Integer(y_range.second), "y");
    auto out = p.create_integer_variable(Integer(out_range.first), Integer(out_range.second), "out");

    auto wrap = [&](SimpleIntegerVariableID v, int m, int o) -> IntegerVariableID {
        IntegerVariableID result = v;
        if (m == -1)
            result = -result;
        return result + Integer{o};
    };
    post_divmod(p, is_div, wrap(x, m1, o1), wrap(y, m2, o2), wrap(out, m3, o3), level);

    auto proof_name = proofs ? make_optional("divide_modulus_test") : nullopt;

    if (check_gac)
        solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{x, y, out});
    else
        solve_for_tests(p, proof_name, actual, tuple{x, y, out});

    check_results(proof_name, expected, actual);
}

// Aliased shapes: x op x = out, x op y = x, and y op x = x.
auto run_divmod_alias_test(bool proofs, bool is_div, const DivideConsistency & level, bool check_gac, const string & shape, pair<int, int> x_range,
    pair<int, int> y_range) -> void
{
    print(cerr, "{} {} {} alias {} {} {} {}", is_div ? "divide" : "modulus", level_name(level), check_gac ? "gac-checked" : "plain", shape, x_range,
        y_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    Problem p;
    auto x = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second), "x");
    auto y = p.create_integer_variable(Integer(y_range.first), Integer(y_range.second), "y");

    auto op_ok = [&](int a, int b, int c) { return is_div ? div_ok(a, b, c) : mod_ok(a, b, c); };

    set<tuple<int, int>> expected, actual;
    if (shape == "xxy") {
        build_expected(expected, [&](int a, int b) { return op_ok(a, a, b); }, x_range, y_range);
        post_divmod(p, is_div, x, x, y, level);
    }
    else if (shape == "xyx") {
        build_expected(expected, [&](int a, int b) { return op_ok(a, b, a); }, x_range, y_range);
        post_divmod(p, is_div, x, y, x, level);
    }
    else if (shape == "yxx") {
        build_expected(expected, [&](int a, int b) { return op_ok(b, a, b); }, x_range, y_range);
        post_divmod(p, is_div, y, x, y, level);
    }
    else
        throw UnexpectedException{"unknown alias shape"};

    println(cerr, " expecting {} solutions", expected.size());

    auto proof_name = proofs ? make_optional("divide_modulus_test") : nullopt;

    if (check_gac)
        solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{x, y});
    else
        solve_for_tests(p, proof_name, actual, tuple{x, y});

    check_results(proof_name, expected, actual);
}

// One slot is a constant: divisor (including zero and negative), dividend, or
// result.
auto run_divmod_constant_test(bool proofs, bool is_div, const DivideConsistency & level, const string & which, int constant, pair<int, int> a_range,
    pair<int, int> b_range) -> void
{
    print(cerr, "{} {} constant {} c={} {} {} {}", is_div ? "divide" : "modulus", level_name(level), which, constant, a_range, b_range,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    Problem p;
    auto a = p.create_integer_variable(Integer(a_range.first), Integer(a_range.second), "a");
    auto b = p.create_integer_variable(Integer(b_range.first), Integer(b_range.second), "b");
    auto c = constant_variable(Integer{constant});

    auto op_ok = [&](int av, int bv, int cv) { return is_div ? div_ok(av, bv, cv) : mod_ok(av, bv, cv); };

    set<tuple<int, int>> expected, actual;
    if (which == "y") {
        build_expected(expected, [&](int av, int bv) { return op_ok(av, constant, bv); }, a_range, b_range);
        post_divmod(p, is_div, a, c, b, level);
    }
    else if (which == "x") {
        build_expected(expected, [&](int av, int bv) { return op_ok(constant, av, bv); }, a_range, b_range);
        post_divmod(p, is_div, c, a, b, level);
    }
    else if (which == "out") {
        build_expected(expected, [&](int av, int bv) { return op_ok(av, bv, constant); }, a_range, b_range);
        post_divmod(p, is_div, a, b, c, level);
    }
    else
        throw UnexpectedException{"unknown constant slot"};

    println(cerr, " expecting {} solutions", expected.size());

    auto proof_name = proofs ? make_optional("divide_modulus_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{a, b});
    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<DivideConsistency> levels{consistency::Auto{}, consistency::BC{}, consistency::Tabulated{}};

    // Random instances for the forced-BC variant: soundness and completeness
    // against a full enumeration, no per-node claim (the decomposition is
    // weaker than bounds consistency on the division itself). The first
    // generator's divisor range spans zero, exercising the relational
    // divisor != 0 handling; the second keeps it strictly positive.
    random_device rand_dev;
    mt19937 rand(rand_dev());
    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>>> random_bc_data;
    for (int x = 0; x < 4; ++x) {
        generate_random_data(rand, random_bc_data, random_bounds(-12, 12, 3, 10), random_bounds(-5, 5, 2, 8), random_bounds(-12, 12, 3, 10));
        generate_random_data(rand, random_bc_data, random_bounds(0, 30, 5, 20), random_bounds(1, 8, 1, 5), random_bounds(-5, 30, 5, 15));
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        for (bool is_div : {true, false}) {
            for (const auto & level : levels) {
                bool force_gac = holds_alternative<consistency::Tabulated>(level);
                bool is_bc = holds_alternative<consistency::BC>(level);

                // Small enough that Auto tabulates (the enumeration tree
                // includes the auxiliary quotient/remainder slot).
                run_divmod_test(proofs, is_div, level, ! is_bc, {0, 2}, {1, 2}, {-1, 2});
                run_divmod_test(proofs, is_div, level, ! is_bc, {-2, 0}, {1, 2}, {-2, 0});

                // Divisor domain spanning zero: only +-1 can support anything,
                // and zero is pruned relationally.
                run_divmod_test(proofs, is_div, level, ! is_bc, {0, 1}, {-1, 1}, {-2, 2});

                // Views on each slot.
                run_divmod_test(proofs, is_div, level, ! is_bc, {0, 2}, {0, 1}, {-1, 2}, {1, -1, 1, 1, -1, 1});

                // Negative divisors, mixed signs: GAC-checked only when
                // forced, since the tree is over the Auto threshold.
                run_divmod_test(proofs, is_div, level, force_gac, {-3, 3}, {-2, 2}, {-3, 3});

                // Aliased shapes.
                run_divmod_alias_test(proofs, is_div, level, ! is_bc, "xxy", {-2, 2}, {-1, 2});
                run_divmod_alias_test(proofs, is_div, level, force_gac, "xyx", {-2, 2}, {-2, 2});
                run_divmod_alias_test(proofs, is_div, level, force_gac, "yxx", {-2, 2}, {-2, 2});

                // Constants in each slot, including the relational
                // divide-by-constant-zero case (no solutions, not an error).
                run_divmod_constant_test(proofs, is_div, level, "y", 3, {-7, 7}, {-3, 3});
                run_divmod_constant_test(proofs, is_div, level, "y", -2, {-5, 5}, {-3, 3});
                run_divmod_constant_test(proofs, is_div, level, "y", 0, {-2, 2}, {-2, 2});
                run_divmod_constant_test(proofs, is_div, level, "x", 7, {-3, 3}, {-7, 7});
                run_divmod_constant_test(proofs, is_div, level, "out", 2, {-8, 8}, {-3, 3});
            }

            // Random instances, forced BC.
            for (const auto & [r1, r2, r3] : random_bc_data)
                run_divmod_test(proofs, is_div, consistency::BC{}, false, r1, r2, r3);

            // Wider domains: Auto falls back on the bounds consistent
            // decomposition; soundness and completeness still checked.
            run_divmod_test(proofs, is_div, consistency::Auto{}, false, {-20, 20}, {-6, 6}, {-20, 20});
            run_divmod_test(proofs, is_div, consistency::Auto{}, false, {0, 50}, {1, 9}, {0, 50});
        }
    }

    return EXIT_SUCCESS;
}
