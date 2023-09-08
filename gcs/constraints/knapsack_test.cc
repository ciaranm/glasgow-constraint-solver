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

auto check_results(const set<tuple<int, int, vector<int>>> & expected, const set<tuple<int, int, vector<int>>> & actual) -> bool
{
    if (expected != actual) {
        cerr << "expected != actual, expected " << expected.size() << " solutions, got " << actual.size() << endl;
        for (auto & e : expected)
            if (! actual.contains(e)) {
                cerr << "missing: " << get<0>(e) << " " << get<1>(e);
                for (auto & v : get<2>(e))
                    cerr << " " << v;
                cerr << endl;
            }
        return false;
    }

    if (0 != system("veripb knapsack_test.opb knapsack_test.veripb"))
        return false;

    return true;
}

auto run_knapsack_test(const vector<int> & weights, const vector<int> & profits, pair<int, int> weight_bounds, pair<int, int> profit_bounds) -> bool
{
    cerr << "knapsack ";
    for (auto & w : weights)
        cerr << w << " ";
    cerr << "/ ";
    for (auto & p : profits)
        cerr << p << " ";
    cerr << "/ " << weight_bounds.first << " / " << weight_bounds.second << " / " << profit_bounds.first << " / " << profit_bounds.second << endl;

    set<tuple<int, int, vector<int>>> expected, actual;
    function<auto(int, vector<int>)->void> build = [&](int pos, vector<int> sol) {
        if (cmp_equal(pos, weights.size())) {
            int w = 0, p = 0;
            for (const auto & [x, s] : enumerate(sol)) {
                w += weights[x] * s;
                p += profits[x] * s;
            }
            if (w >= weight_bounds.first && w <= weight_bounds.second && p >= profit_bounds.first && p <= profit_bounds.second)
                expected.emplace(w, p, sol);
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
    auto vs = p.create_integer_variable_vector(weights.size(), 0_i, 1_i);
    auto profit = p.create_integer_variable(Integer(profit_bounds.first), Integer(profit_bounds.second));
    auto weight = p.create_integer_variable(Integer(weight_bounds.first), Integer(weight_bounds.second));
    vector<Integer> weights_integers, profits_integers;
    for (auto & w : weights)
        weights_integers.push_back(Integer(w));
    for (auto & p : profits)
        profits_integers.push_back(Integer(p));
    p.post(Knapsack{weights_integers, profits_integers, vs, weight, profit});
    solve(
        p, [&](const CurrentState & s) -> bool {
            vector<int> sol;
            for (auto & v : vs)
                sol.push_back(s(v).raw_value);
            actual.emplace(s(weight).raw_value, s(profit).raw_value, sol);
            return true;
        },
        ProofOptions{"knapsack_test.opb", "knapsack_test.veripb"});

    return check_results(expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<vector<int>, vector<int>, pair<int, int>, pair<int, int>>> data = {
        {{2, 3, 4}, {2, 3, 4}, {0, 8}, {3, 1000}},
        {{2, 3, 4}, {2, 3, 4}, {3, 8}, {3, 1000}},
        {{2, 3, 4}, {2, 3, 4}, {0, 8}, {3, 5}},
        {{1, 3, 4}, {2, 0, 8}, {0, 8}, {3, 1000}},
        {{2, 0, 8}, {1, 3, 4}, {0, 8}, {3, 1000}},
        {{2, 0, 8}, {2, 0, 8}, {0, 8}, {3, 1000}},
        {{2, 2, 2, 2, 2}, {2, 2, 2, 2, 2}, {0, 5}, {5, 1000}},
        {{3, 3, 2, 3}, {2, 5, 6, 8}, {0, 7}, {4, 1000}},
        {{8, 2, 4, 3}, {6, 5, 5, 6}, {0, 4}, {13, 1000}},
        {{5, 4, 8, 7}, {2, 5, 1, 5}, {0, 12}, {5, 1000}},
        {{8, 7, 4, 8}, {4, 3, 4, 4}, {0, 18}, {10, 1000}},
        {{7, 4, 4, 7}, {1, 2, 1, 0}, {18, 19}, {3, 8}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution size_dist(1, 4), item_dist(0, 8), bound_dist(0, 40), delta_dist(0, 30);
        auto size = size_dist(rand);
        vector<int> w, p;
        for (auto i = 0; i < size; ++i) {
            w.push_back(item_dist(rand));
            p.push_back(item_dist(rand));
        }
        auto wb = bound_dist(rand), pb = bound_dist(rand);
        data.emplace_back(w, p, pair{max(0, wb - delta_dist(rand)), wb}, pair{pb, pb + delta_dist(rand)});
    }

    for (auto & [weights, profits, weight_bounds, profit_bounds] : data)
        if (! run_knapsack_test(weights, profits, weight_bounds, profit_bounds))
            return EXIT_FAILURE;

    return EXIT_SUCCESS;
}
