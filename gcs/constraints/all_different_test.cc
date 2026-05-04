#include <gcs/constraints/all_different.hh>
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

auto run_all_different_test(bool proofs, variant<int, pair<int, int>> v1_range, variant<int, pair<int, int>> v2_range, variant<int, pair<int, int>> v3_range,
    variant<int, pair<int, int>> v4_range, variant<int, pair<int, int>> v5_range, variant<int, pair<int, int>> v6_range) -> void
{
    // if this crashes your compiler, implement print for variant instead...
    visit([&](auto v1, auto v2, auto v3, auto v4, auto v5, auto v6) {
        print(cerr, "all_different {} {} {} {} {} {} {}", v1, v2, v3, v4, v5, v6, proofs ? " with proofs:" : ":");
    },
        v1_range, v2_range, v3_range, v4_range, v5_range, v6_range);
    cerr << flush;

    auto is_satisfying = [](int a, int b, int c, int d, int e, int f) {
        return a != b && a != c && a != d && a != e && a != f && b != c && b != d && b != e && b != f && c != d && c != e && c != f && d != e && d != f && e != f;
    };

    set<tuple<int, int, int, int, int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range, v4_range, v5_range, v6_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v1_range);
    auto v2 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v2_range);
    auto v3 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v3_range);
    auto v4 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v4_range);
    auto v5 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v5_range);
    auto v6 = visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, v6_range);
    p.post(AllDifferent{vector<IntegerVariableID>{v1, v2, v3, v4, v5, v6}});

    auto proof_name = proofs ? make_optional("all_different_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3, v4, v5, v6});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<variant<int, pair<int, int>>, variant<int, pair<int, int>>, variant<int, pair<int, int>>,
        variant<int, pair<int, int>>, variant<int, pair<int, int>>, variant<int, pair<int, int>>>>
        data = {
            {pair{1, 6}, pair{1, 6}, pair{1, 6}, pair{1, 6}, pair{1, 6}, pair{1, 6}},
            {pair{0, 5}, pair{1, 6}, pair{2, 7}, pair{3, 8}, pair{4, 9}, pair{5, 6}},
            // issue #108: constants in hall set crash prove_matching_is_too_small
            {pair{-2, 3}, 5, pair{3, 5}, pair{3, 6}, 3, pair{3, 5}},
            // issue #108: constants in hall set crash prove_deletion_using_sccs
            {pair{1, 2}, pair{1, 2}, 3, pair{3, 4}, pair{4, 5}, pair{5, 6}}};

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
        generate_random_data(rand, data, random_constant(-10, 10), random_constant(-10, 10), random_constant(-10, 10),
            random_constant(-10, 10), random_constant(-10, 10), random_constant(-10, 10));

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2, r3, r4, r5, r6] : data)
            run_all_different_test(proofs, r1, r2, r3, r4, r5, r6);
    }

    return EXIT_SUCCESS;
}
