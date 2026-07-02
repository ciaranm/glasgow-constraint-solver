#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
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
using std::function;
using std::is_same_v;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::optional;
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
    template <typename Arithmetic_>
    struct NameOf;

    template <>
    struct NameOf<PlusGAC>
    {
        static const constexpr auto name = "plusgac";
    };

    template <>
    struct NameOf<MinusGAC>
    {
        static const constexpr auto name = "minusgac";
    };

}

template <typename Arithmetic_>
auto run_arithmetic_test(bool proofs, pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range,
    const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    print(cerr, "arithmetic {} {} {} {} {}", NameOf<Arithmetic_>::name, v1_range, v2_range, v3_range, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
    p.post(Arithmetic_{v1, v2, v3});

    auto proof_name = proofs ? make_optional("arithmetic_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

// Dup-variable tests: post a GACArithmetic constraint with the same handle
// in two (or all three) slots. The GAC algorithm operates over a tuple
// table that doesn't know two slots alias, so consistency on alias drops
// to "weak"; we don't check it. See tmp/duplicate_var_audit.md.
namespace
{
    struct AliasV1V2
    {
    };
    struct AliasV1V3
    {
    };
    struct AliasV2V3
    {
    };
    struct AliasAll
    {
    };
}

template <typename Arithmetic_, typename AliasPattern_>
auto run_dup_arithmetic_test(bool proofs, AliasPattern_, const string & tag, pair<int, int> a_range, pair<int, int> b_range,
    const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    print(cerr, "arithmetic {} dup {} {} {} {}", NameOf<Arithmetic_>::name, tag, a_range, b_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    Problem p;
    auto proof_name = proofs ? make_optional(string{"arithmetic_test_"} + NameOf<Arithmetic_>::name + "_dup_" + tag) : nullopt;

    if constexpr (is_same_v<AliasPattern_, AliasAll>) {
        set<tuple<int>> expected, actual;
        build_expected(expected, [&](int a) { return is_satisfying(a, a, a); }, a_range);
        println(cerr, " expecting {} solutions", expected.size());

        auto a = p.create_integer_variable(Integer(a_range.first), Integer(a_range.second));
        p.post(Arithmetic_{a, a, a});

        solve_for_tests(p, proof_name, actual, tuple{a});
        check_results(proof_name, expected, actual);
    }
    else {
        set<tuple<int, int>> expected, actual;
        if constexpr (is_same_v<AliasPattern_, AliasV1V2>)
            build_expected(expected, [&](int a, int b) { return is_satisfying(a, a, b); }, a_range, b_range);
        else if constexpr (is_same_v<AliasPattern_, AliasV1V3>)
            build_expected(expected, [&](int a, int b) { return is_satisfying(a, b, a); }, a_range, b_range);
        else
            build_expected(expected, [&](int a, int b) { return is_satisfying(a, b, b); }, a_range, b_range);
        println(cerr, " expecting {} solutions", expected.size());

        auto a = p.create_integer_variable(Integer(a_range.first), Integer(a_range.second));
        auto b = p.create_integer_variable(Integer(b_range.first), Integer(b_range.second));
        if constexpr (is_same_v<AliasPattern_, AliasV1V2>)
            p.post(Arithmetic_{a, a, b});
        else if constexpr (is_same_v<AliasPattern_, AliasV1V3>)
            p.post(Arithmetic_{a, b, a});
        else
            p.post(Arithmetic_{a, b, b});

        solve_for_tests(p, proof_name, actual, tuple{a, b});
        check_results(proof_name, expected, actual);
    }
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>>> data = {{{2, 5}, {1, 6}, {1, 12}}, //
        {{1, 6}, {2, 5}, {5, 8}},                                                                    //
        {{1, 3}, {1, 3}, {0, 10}},                                                                   //
        {{1, 3}, {1, 3}, {1, 3}},                                                                    //
        {{1, 5}, {6, 8}, {-10, 10}},                                                                 //
        {{1, 1}, {2, 4}, {-5, 5}},                                                                   //
        // issue #254: all-fixed (singleton-domain) operands. Each row runs for
        // Plus/Minus; build_expected gives the per-operation truth, so
        // each tautology direction is hit by exactly one operation and the
        // others act as the contradiction direction. (The multiplication row
        // lives on as a contradiction row; Multiply has its own test.)
        {{2, 2}, {3, 3}, {5, 5}},    // Plus: 2+3==5
        {{5, 5}, {2, 2}, {3, 3}},    // Minus: 5-2==3
        {{2, 2}, {3, 3}, {6, 6}},    // 2*3==6, contradiction for the others
        {{6, 6}, {3, 3}, {2, 2}},    // 6/3==2, contradiction for the others
        {{7, 7}, {3, 3}, {1, 1}},    // 7%3==1, contradiction for the others
        {{5, 5}, {0, 0}, {3, 3}},    // zero middle operand
        {{5, 5}, {2, 2}, {99, 99}}}; // all operations contradicted

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2, r3] : data) {
            run_arithmetic_test<PlusGAC>(proofs, r1, r2, r3, [](int a, int b, int c) { return a + b == c; });
            run_arithmetic_test<MinusGAC>(proofs, r1, r2, r3, [](int a, int b, int c) { return a - b == c; });
        }

        // Dup-variable cases for the GAC-via-Table specialisations. Domains
        // are kept small because the underlying tuple table is materialised.
        // (The division-family dup cases live in divide_modulus_test now.)
        vector<pair<pair<int, int>, pair<int, int>>> dup_data = {
            {{-3, 3}, {-9, 9}}, //
            {{1, 4}, {-5, 5}}   //
        };
        auto plus_sat = [](int a, int b, int c) { return a + b == c; };
        auto minus_sat = [](int a, int b, int c) { return a - b == c; };
        for (auto & [ar, br] : dup_data) {
            run_dup_arithmetic_test<PlusGAC>(proofs, AliasV1V2{}, "v1v2", ar, br, plus_sat);
            run_dup_arithmetic_test<PlusGAC>(proofs, AliasV1V3{}, "v1v3", ar, br, plus_sat);
            run_dup_arithmetic_test<PlusGAC>(proofs, AliasV2V3{}, "v2v3", ar, br, plus_sat);
            run_dup_arithmetic_test<PlusGAC>(proofs, AliasAll{}, "all", ar, br, plus_sat);
            run_dup_arithmetic_test<MinusGAC>(proofs, AliasV1V2{}, "v1v2", ar, br, minus_sat);
            run_dup_arithmetic_test<MinusGAC>(proofs, AliasV1V3{}, "v1v3", ar, br, minus_sat);
            run_dup_arithmetic_test<MinusGAC>(proofs, AliasV2V3{}, "v2v3", ar, br, minus_sat);
            run_dup_arithmetic_test<MinusGAC>(proofs, AliasAll{}, "all", ar, br, minus_sat);
        }
    }

    return EXIT_SUCCESS;
}
