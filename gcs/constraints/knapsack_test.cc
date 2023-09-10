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

using std::cerr;
using std::cmp_equal;
using std::endl;
using std::function;
using std::max;
using std::mt19937;
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::to_string;
using std::tuple;
using std::uniform_int_distribution;
using std::vector;

using namespace gcs;

auto check_results(const set<tuple<vector<int>, vector<int>>> & expected, const set<tuple<vector<int>, vector<int>>> & actual) -> bool
{
    if (expected != actual) {
        cerr << "expected != actual, expected " << expected.size() << " solutions, got " << actual.size() << endl;
        for (auto & e : expected)
            if (! actual.contains(e)) {
                cerr << "missing: ";
                for (auto & v : get<1>(e))
                    cerr << " " << v;
                cerr << endl;
            }
        return false;
    }

    if (0 != system("veripb knapsack_test.opb knapsack_test.veripb"))
        return false;

    return true;
}

auto run_knapsack_test(const vector<vector<int>> & coeffs, const vector<pair<int, int>> & bounds) -> bool
{
    cerr << "knapsack ";
    for (const auto & c : coeffs) {
        cerr << "[";
        for (auto & w : c)
            cerr << " " << w << " ";
        cerr << "]";
    }

    for (const auto & b : bounds) {
        cerr << " (" << b.first << ", " << b.second << ")";
    }
    cerr << endl;

    set<tuple<vector<int>, vector<int>>> expected, actual;
    function<auto(int, vector<int>)->void> build = [&](int pos, vector<int> sol) {
        if (cmp_equal(pos, coeffs[0].size())) {
            vector<int> sums(coeffs.size(), 0);
            for (const auto & [x, s] : enumerate(sol)) {
                for (unsigned i = 0; i < coeffs.size(); ++i)
                    sums[i] += coeffs[i][x] * s;
            }

            bool feasible = true;
            for (unsigned i = 0; i < coeffs.size(); ++i)
                if (! (sums[i] >= bounds[i].first && sums[i] <= bounds[i].second)) {
                    feasible = false;
                    break;
                }

            if (feasible)
                expected.emplace(sums, sol);
        }
        else {
            sol.push_back(0);
            build(pos + 1, sol);
            sol.pop_back();

            sol.push_back(1);
            build(pos + 1, sol);
            sol.pop_back();
        }
    };
    build(0, {});

    Problem p;
    auto vs = p.create_integer_variable_vector(coeffs[0].size(), 0_i, 1_i);
    vector<IntegerVariableID> bs;
    for (unsigned i = 0; i < coeffs.size(); ++i)
        bs.push_back(p.create_integer_variable(Integer(bounds[i].first), Integer(bounds[i].second)));
    vector<vector<Integer>> coeffs_integers(coeffs.size());
    for (unsigned i = 0; i < coeffs.size(); ++i)
        for (const auto & w : coeffs[i])
            coeffs_integers[i].push_back(Integer(w));

    p.post(Knapsack{coeffs_integers, vs, bs});
    solve(
        p, [&](const CurrentState & s) -> bool {
            vector<int> sol, bounds;
            for (auto & v : vs)
                sol.push_back(s(v).raw_value);
            for (unsigned i = 0; i < coeffs.size(); ++i)
                bounds.push_back(s(bs[i]).raw_value);
            actual.emplace(bounds, sol);
            return true;
        },
        ProofOptions{"knapsack_test.opb", "knapsack_test.veripb"});

    return check_results(expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<vector<vector<int>>, vector<pair<int, int>>>> data = {
        {{{2, 3, 4}, {2, 3, 4}}, {{0, 8}, {3, 1000}}},
        {{{2, 3, 4}, {2, 3, 4}}, {{3, 8}, {3, 1000}}},
        {{{2, 3, 4}, {2, 3, 4}}, {{0, 8}, {3, 5}}},
        {{{1, 3, 4}, {2, 0, 8}}, {{0, 8}, {3, 1000}}},
        {{{2, 0, 8}, {1, 3, 4}}, {{0, 8}, {3, 1000}}},
        {{{2, 0, 8}, {2, 0, 8}}, {{0, 8}, {3, 1000}}},
        {{{2, 2, 2, 2, 2}, {2, 2, 2, 2, 2}}, {{0, 5}, {5, 1000}}},
        {{{3, 3, 2, 3}, {2, 5, 6, 8}}, {{0, 7}, {4, 1000}}},
        {{{8, 2, 4, 3}, {6, 5, 5, 6}}, {{0, 4}, {13, 1000}}},
        {{{5, 4, 8, 7}, {2, 5, 1, 5}}, {{0, 12}, {5, 1000}}},
        {{{8, 7, 4, 8}, {4, 3, 4, 4}}, {{0, 18}, {10, 1000}}},
        {{{7, 4, 4, 7}, {1, 2, 1, 0}}, {{18, 19}, {3, 8}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_coeffs_dist(1, 4), size_dist(1, 4), item_dist(0, 8), bound_dist(0, 40), delta_dist(0, 30);
        auto size = size_dist(rand);
        auto n_coeffs = n_coeffs_dist(rand);
        vector<vector<int>> c(n_coeffs);
        for (auto i = 0; i < size; ++i)
            for (int k = 0; k < n_coeffs; ++k)
                c[k].push_back(item_dist(rand));

        vector<pair<int, int>> boundses;
        for (unsigned k = 0; k < n_coeffs; ++k) {
            auto wb = bound_dist(rand);
            boundses.emplace_back(max(0, wb - delta_dist(rand)), wb);
        }
        data.emplace_back(c, boundses);
    }

    for (auto & [coeffs, bounds] : data)
        if (! run_knapsack_test(coeffs, bounds))
            return EXIT_FAILURE;

    return EXIT_SUCCESS;
}
