#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/knapsack.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <util/enumerate.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>

using std::cerr;
using std::cmp_equal;
using std::flush;
using std::function;
using std::make_optional;
using std::max;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::to_string;
using std::tuple;
using std::uniform_int_distribution;
using std::vector;

using fmt::print;
using fmt::println;

using namespace gcs;
using namespace gcs::test_innards;

auto run_knapsack_test(bool proofs, pair<int, int> valrange, const vector<vector<int>> & coeffs, const vector<pair<int, int>> & bounds) -> void
{
    print(cerr, "knapsack {} {} {} {}", valrange, coeffs, bounds, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, vector<int>>> expected, actual;

    auto is_satisfing = [&](const vector<int> & taken, const vector<int> & profits) {
        vector<int> sums(coeffs.size(), 0);
        for (const auto & [x, s] : enumerate(taken))
            for (unsigned i = 0; i < coeffs.size(); ++i)
                sums[i] += coeffs[i][x] * s;

        for (unsigned i = 0; i < coeffs.size(); ++i)
            if (! (sums[i] >= bounds[i].first && sums[i] <= bounds[i].second))
                return false;

        return sums == profits;
    };
    build_expected(expected, is_satisfing, vector{coeffs[0].size(), valrange}, bounds);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto vs = p.create_integer_variable_vector(coeffs[0].size(), Integer(valrange.first), Integer(valrange.second));
    vector<IntegerVariableID> bs;
    for (unsigned i = 0; i < coeffs.size(); ++i)
        bs.push_back(p.create_integer_variable(Integer(bounds[i].first), Integer(bounds[i].second)));
    vector<vector<Integer>> coeffs_integers(coeffs.size());
    for (unsigned i = 0; i < coeffs.size(); ++i)
        for (const auto & w : coeffs[i])
            coeffs_integers[i].push_back(Integer(w));

    p.post(Knapsack{coeffs_integers, vs, bs});

    auto proof_name = proofs ? make_optional("knapsack_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vs, bs});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, vector<vector<int>>, vector<pair<int, int>>>> data = {
        {{0, 1}, {{2, 3, 4}, {2, 3, 4}}, {{0, 8}, {3, 1000}}},
        {{0, 1}, {{2, 3, 4}, {2, 3, 4}}, {{3, 8}, {3, 1000}}},
        {{0, 1}, {{2, 3, 4}, {2, 3, 4}}, {{0, 8}, {3, 5}}},
        {{0, 1}, {{1, 3, 4}, {2, 0, 8}}, {{0, 8}, {3, 1000}}},
        {{0, 1}, {{2, 0, 8}, {1, 3, 4}}, {{0, 8}, {3, 1000}}},
        {{0, 1}, {{2, 0, 8}, {2, 0, 8}}, {{0, 8}, {3, 1000}}},
        {{0, 1}, {{2, 2, 2, 2, 2}, {2, 2, 2, 2, 2}}, {{0, 5}, {5, 1000}}},
        {{0, 1}, {{3, 3, 2, 3}, {2, 5, 6, 8}}, {{0, 7}, {4, 1000}}},
        {{0, 1}, {{8, 2, 4, 3}, {6, 5, 5, 6}}, {{0, 4}, {13, 1000}}},
        {{0, 1}, {{5, 4, 8, 7}, {2, 5, 1, 5}}, {{0, 12}, {5, 1000}}},
        {{0, 1}, {{8, 7, 4, 8}, {4, 3, 4, 4}}, {{0, 18}, {10, 1000}}},
        {{0, 1}, {{7, 4, 4, 7}, {1, 2, 1, 0}}, {{18, 19}, {3, 8}}},
        {{2, 4}, {{4, 1, 2, 3}, {4, 6, 3, 8}, {5, 3, 1, 6}}, {{0, 64}, {0, 48}, {0, 41}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_coeffs_dist(1, 4), size_dist(1, 4), item_dist(0, 8), bound_dist(0, 40), delta_dist(0, 30);
        auto size = size_dist(rand);
        auto n_coeffs = n_coeffs_dist(rand);

        vector<pair<int, int>> boundses;
        for (int k = 0; k < n_coeffs; ++k) {
            auto wb = bound_dist(rand) + 20;
            boundses.emplace_back(max(0, wb - (25 + delta_dist(rand))), wb);
        }

        generate_random_data(rand, data, random_bounds(0, 2, 1, 3), vector(n_coeffs, vector(size, item_dist)), boundses);
    }

    for (auto & [valrange, coeffs, bounds] : data)
        run_knapsack_test(false, valrange, coeffs, bounds);

    if (can_run_veripb())
        for (auto & [valrange, coeffs, bounds] : data)
            run_knapsack_test(true, valrange, coeffs, bounds);

    return EXIT_SUCCESS;
}
