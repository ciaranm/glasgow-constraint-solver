#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/min_max.hh>
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
using std::random_device;
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

auto run_min_max_test(bool proofs, bool min, variant<int, pair<int, int>> result_range, const vector<variant<int, pair<int, int>>> & array_range) -> void
{
    visit([&](auto r) { print(cerr, "{} {} {} {}", min ? "min" : "max", r, array_range, proofs ? " with proofs:" : ":"); }, result_range);
    cerr << flush;

    auto is_satisfying = [&](int r, const vector<int> & a) {
        return (! a.empty()) && (min ? (*min_element(a.begin(), a.end()) == r) : (*max_element(a.begin(), a.end()) == r));
    };

    set<pair<int, vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, result_range, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto result = visit([&](auto r) { return create_integer_variable_or_constant(p, r); }, result_range);
    vector<IntegerVariableID> array;
    for (const auto & entry : array_range)
        array.push_back(visit([&](auto e) { return create_integer_variable_or_constant(p, e); }, entry));
    if (min)
        p.post(ArrayMin{array, result});
    else
        p.post(ArrayMax{array, result});

    auto proof_name = proofs ? make_optional("min_max_test") : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{result, CheckConsistency::GAC}, pair{array, CheckConsistency::GAC}});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    using ArrayEntry = variant<int, pair<int, int>>;
    vector<tuple<variant<int, pair<int, int>>, vector<ArrayEntry>>> data = {
        // Singleton: result must equal the sole element.
        {pair{1, 5}, {pair{2, 4}}},
        {3, {pair{0, 5}}},
        {pair{1, 2}, {pair{1, 2}, pair{1, 2}}},
        {pair{1, 2}, {pair{1, 2}, pair{1, 2}, pair{1, 2}}},
        {pair{0, 4}, {pair{1, 2}, pair{1, 2}, pair{1, 2}}},
        {pair{1, 3}, {pair{0, 4}, pair{0, 5}, pair{0, 6}}},
        {pair{-1, 3}, {pair{-1, 2}, pair{1, 3}, pair{4, 5}}},
        {pair{1, 4}, {pair{1, 4}, pair{2, 3}, pair{0, 5}, pair{-2, 0}, pair{5, 7}}},
        {pair{-5, 5}, {pair{-8, 0}, pair{4, 4}, pair{10, 10}, pair{2, 11}, pair{4, 10}}},
        {pair{0, 5}, {pair{4, 12}}},
        {pair{2, 9}, {pair{-2, 3}, pair{-4, -1}, pair{-3, 5}}},
        {pair{2, 5}, {pair{2, 4}, pair{3, 7}, pair{1, 4}}},
        {pair{-3, 2}, {pair{-1, 7}, pair{-2, 6}, pair{1, 8}, pair{4, 11}}},
        // Constant array entries: forced winner / fixed pivot.
        {pair{-5, 10}, {3, pair{0, 7}, 5}},
        {pair{-5, 10}, {pair{0, 4}, 7, pair{1, 6}, pair{2, 9}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
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

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2] : data) {
            run_min_max_test(proofs, false, r1, r2);
            run_min_max_test(proofs, true, r1, r2);
        }
    }

    return EXIT_SUCCESS;
}
