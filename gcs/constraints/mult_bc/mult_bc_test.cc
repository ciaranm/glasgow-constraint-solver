#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/mult_bc.hh>
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
#include <tuple>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::function;
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

auto run_mult_test(bool proofs, pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range,
    const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    print(cerr, "mult {} {} {} {}", v1_range, v2_range, v3_range, proofs ? " with proofs:" : ":");
    cerr << flush;
    set<tuple<int, int, int>> expected, actual;

    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second), "v1");
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second), "v2");
    auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second), "v3");
    p.post(MultBC{v1, v2, v3});

    auto proof_name = proofs ? make_optional("mult_bc_test") : nullopt;

    // TODO: Check for bounds(R)-consistency (currently the check is for bounds(Z))
    solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

// MultBC's bit-product proof encoding doesn't tolerate aliased
// operands. Construction throws InvalidProblemDefinitionException
// rather than failing later under VeriPB.
auto expect_mult_alias_throws(const char * tag, int v1_pos, int v2_pos, int v3_pos) -> bool
{
    Problem p;
    auto a = p.create_integer_variable(-3_i, 3_i, "a");
    auto b = p.create_integer_variable(-3_i, 3_i, "b");
    auto pick = [&](int pos) { return pos == 0 ? a : b; };
    try {
        p.post(MultBC{pick(v1_pos), pick(v2_pos), pick(v3_pos)});
    }
    catch (const InvalidProblemDefinitionException &) {
        return true;
    }
    println(cerr, "MultBC dup {} expected InvalidProblemDefinitionException", tag);
    return false;
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>>> data = {{{2, 5}, {1, 6}, {1, 12}}, {{1, 6}, {2, 5}, {5, 8}},
        {{1, 3}, {1, 3}, {0, 10}}, {{1, 3}, {1, 3}, {1, 3}}, {{1, 5}, {6, 8}, {-10, 10}}, {{1, 1}, {2, 4}, {-5, 5}}, {{8, 15}, {-14, 11}, {-9, -4}},
        {{-8, 3}, {-9, 6}, {4, 14}}, {{-10, 2}, {-5, 3}, {4, 9}}, {{9, 23}, {-5, 9}, {9, 14}}, {{-4, 8}, {-8, 7}, {-2, 9}},
        {{-34, -27}, {-10, 2}, {29, 179}},
        // issue #254: all-fixed (singleton-domain) operands, both directions —
        // the product is fully determined, so the constraint reduces to a
        // true/false check.
        {{2, 2}, {3, 3}, {6, 6}},     // 2*3 == 6 (tautology)
        {{2, 2}, {3, 3}, {7, 7}},     // 2*3 != 7 (contradiction)
        {{0, 0}, {5, 5}, {0, 0}},     // 0*5 == 0 (tautology)
        {{-2, -2}, {3, 3}, {-6, -6}}, // -2*3 == -6 (tautology)
        {{-2, -2}, {3, 3}, {6, 6}}};  // -2*3 != 6 (contradiction)

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 5; ++x) {
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));
        generate_random_data(rand, data, random_bounds(-100, 100, 5, 10), random_bounds(-10, 10, 5, 15), random_bounds(-100, 100, 150, 150));
        generate_random_data(rand, data, random_bounds(0, 100, 1, 10), random_bounds(0, 50, 0, 5), random_bounds(0, 1000, 0, 2000));
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2, r3] : data) {
            run_mult_test(proofs, r1, r2, r3, [](int a, int b, int c) { return a * b == c; });
        }
    }

    // Aliased operands throw at construction. Don't tie these to the
    // proofs axis — the throw happens before any proof artifact is
    // emitted.
    bool ok = true;
    ok &= expect_mult_alias_throws("v1==v2", 0, 0, 1);
    ok &= expect_mult_alias_throws("v1==v3", 0, 1, 0);
    ok &= expect_mult_alias_throws("v2==v3", 1, 0, 0);
    {
        Problem p;
        auto x = p.create_integer_variable(-3_i, 3_i, "x");
        try {
            p.post(MultBC{x, x, x});
            println(cerr, "MultBC(x, x, x) expected InvalidProblemDefinitionException");
            ok = false;
        }
        catch (const InvalidProblemDefinitionException &) {
        }
    }

    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
