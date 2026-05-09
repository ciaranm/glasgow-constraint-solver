#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/n_value.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

using std::cerr;
using std::cmp_equal;
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

auto run_n_value_test(bool proofs, variant<int, pair<int, int>> result_range, const vector<variant<int, pair<int, int>>> & array_range) -> void
{
    visit([&](auto r) { print(cerr, "nvalue {} {} {}", r, array_range, proofs ? " with proofs:" : ":"); }, result_range);
    cerr << flush;

    set<tuple<int, vector<int>>> expected, actual;
    auto is_satisfying = [&](int n, const vector<int> & v) -> bool {
        set<int> s{v.begin(), v.end()};
        return cmp_equal(n, s.size());
    };
    build_expected(expected, is_satisfying, result_range, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto result = visit([&](auto r) { return create_integer_variable_or_constant(p, r); }, result_range);
    vector<IntegerVariableID> array;
    for (const auto & entry : array_range)
        array.push_back(visit([&](auto e) { return create_integer_variable_or_constant(p, e); }, entry));
    p.post(NValue{result, array});

    auto proof_name = proofs ? make_optional("n_value_test") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{result, array});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    using ArrayEntry = variant<int, pair<int, int>>;
    vector<tuple<variant<int, pair<int, int>>, vector<ArrayEntry>>> data = {
        // Boundary: empty array forces result == 0.
        {pair{0, 3}, {}},
        {0, {}},
        // Boundary: singleton forces result == 1.
        {pair{0, 3}, {pair{2, 5}}},
        {1, {pair{0, 9}}},
        {pair{1, 2}, {pair{1, 2}, pair{1, 2}}},
        {pair{1, 2}, {pair{1, 2}, pair{1, 2}, pair{1, 2}}},
        {pair{0, 4}, {pair{1, 2}, pair{1, 2}, pair{1, 2}}},
        {pair{1, 3}, {pair{0, 4}, pair{0, 5}, pair{0, 6}}},
        {pair{-1, 3}, {pair{-1, 2}, pair{1, 3}, pair{4, 5}}},
        {pair{1, 4}, {pair{1, 4}, pair{2, 3}, pair{0, 5}, pair{-2, 0}, pair{5, 7}}},
        {pair{-5, 5}, {pair{-8, 0}, pair{4, 4}, pair{10, 10}, pair{2, 11}, pair{4, 10}}},
        // Constant array entries: pinned values count toward distinct.
        {pair{0, 5}, {3, pair{1, 4}, 3}},
        {pair{0, 5}, {1, 2, 3, pair{0, 5}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 5);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_bounds(-5, 5, 2, 7), vector(n_values, random_bounds_or_constant(-5, 5, 2, 7)));
    }

    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 5);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_constant(-5, 5), vector(n_values, random_bounds_or_constant(-5, 5, 2, 7)));
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2] : data)
            run_n_value_test(proofs, r1, r2);
    }

    return EXIT_SUCCESS;
}
