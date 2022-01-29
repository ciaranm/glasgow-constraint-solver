/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include "util/for_each.hh"

#include <cstdlib>
#include <functional>
#include <iostream>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

using std::cerr;
using std::endl;
using std::function;
using std::index_sequence;
using std::make_index_sequence;
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

template <typename T_, size_t... i_>
auto stringify_tuple(const T_ & t, index_sequence<i_...>) -> string
{
    string result = "(";
    (..., (result.append(i_ == 0 ? "" : ", ").append(to_string(get<i_>(t)))));
    result.append(")");
    return result;
}

template <typename... T_>
auto stringify_tuple(const tuple<T_...> & t) -> string
{
    return stringify_tuple(t, make_index_sequence<sizeof...(T_)>());
}

template <typename P_, typename Q_>
auto stringify_tuple(const pair<P_, Q_> & t) -> string
{
    return stringify_tuple(t, make_index_sequence<2>());
}

template <typename Results_>
auto check_results(
    pair<int, int> v0_range,
    pair<int, int> v1_range,
    pair<int, int> v2_range,
    const vector<pair<vector<int>, int>> & constraints,
    const string & name,
    const Results_ & expected,
    const Results_ & actual) -> bool
{
    cerr << name << " " << stringify_tuple(v0_range) << " " << stringify_tuple(v1_range) << " " << stringify_tuple(v2_range)
         << " " << expected.size();
    if (expected != actual) {
        cerr << " expected:";
        for (auto & t : expected) {
            cerr << " " << stringify_tuple(t);
            if (! actual.contains(t))
                cerr << "!";
        }
        cerr << "; actual:";
        for (auto & t : actual) {
            cerr << " " << stringify_tuple(t);
            if (! expected.contains(t))
                cerr << "!";
        }
        cerr << endl;

        cerr << "constraints:" << endl;
        for (auto & [coeffs, val] : constraints) {
            for (auto & c : coeffs)
                cerr << c << " ";
            cerr << "<= " << val << endl;
        }

        return false;
    }
    cerr << endl;

    if (0 != system("veripb linear_equality_test.opb linear_equality_test.veripb"))
        return false;

    return true;
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>, vector<pair<vector<int>, int>>>> data;

    data.emplace_back(
        pair{3, 8}, pair{-4, 7}, pair{2, 5},
        vector{
            pair{vector{2, 3, 4}, 20},
            pair{vector{-1, -3, 0}, -5},
            pair{vector{0, 4, 2}, 6}});

    data.emplace_back(
        pair{3, 8}, pair{-4, 7}, pair{2, 5},
        vector{
            pair{vector{2, 3, 4}, 30},
            pair{vector{-1, -3, 0}, -5},
            pair{vector{0, 4, 2}, 6}});

    data.emplace_back(
        pair{-3, 5}, pair{-3, 5}, pair{-2, 5},
        vector{
            pair{vector{2, 3, 4}, 20},
            pair{vector{-1, -3, 0}, -5},
            pair{vector{0, 4, 2}, 6}});

    data.emplace_back(
        pair{7, 9}, pair{-7, 0}, pair{4, 8},
        vector{
            pair{vector{-3, 3, -5}, -62},
            pair{vector{3, 4, 3}, 197}});

    data.emplace_back(
        pair{3, 4}, pair{8, 12}, pair{5, 13},
        vector{
            pair{vector{-8, -9, -6}, -154},
            pair{vector{8, -9, -9}, 71},
            pair{vector{8, 5, 9}, 175},
            pair{vector{3, -8, 10}, 9},
            pair{vector{6, 4, 5}, 174}});

    data.emplace_back(
        pair{-7, -6}, pair{-9, -2}, pair{-4, 3},
        vector{
            pair{vector{9, -9, -8}, 90},
            pair{vector{6, 1, -5}, 188},
            pair{vector{10, 8, -10}, 67},
            pair{vector{-2, -8, 0}, 138},
            pair{vector{10, 4, 7}, -78}});

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution r1_lower_dist(-10, 10);
        auto r1_lower = r1_lower_dist(rand);
        uniform_int_distribution r1_upper_dist(r1_lower, r1_lower + 10);
        auto r1_upper = r1_upper_dist(rand);

        uniform_int_distribution r2_lower_dist(-10, 10);
        auto r2_lower = r2_lower_dist(rand);
        uniform_int_distribution r2_upper_dist(r2_lower, r2_lower + 10);
        auto r2_upper = r2_upper_dist(rand);

        uniform_int_distribution r3_lower_dist(-10, 10);
        auto r3_lower = r3_lower_dist(rand);
        uniform_int_distribution r3_upper_dist(r3_lower, r3_lower + 10);
        auto r3_upper = r3_upper_dist(rand);

        vector<pair<vector<int>, int>> constraints;
        uniform_int_distribution c_dist(2, 5);
        for (int c = 0, c_end = c_dist(rand); c != c_end; ++c) {
            vector<int> lin;
            for (int v = 0; v < 3; ++v) {
                uniform_int_distribution coeff_dist(-10, 10);
                lin.push_back(coeff_dist(rand));
            }
            uniform_int_distribution val_dist(-200, 200);
            constraints.emplace_back(move(lin), val_dist(rand));
        }
        data.emplace_back(pair{r1_lower, r1_upper}, pair{r2_lower, r2_upper}, pair{r3_lower, r3_upper},
            move(constraints));
    }

    for (auto & [v0_range, v1_range, v2_range, constraints] : data) {
        set<tuple<int, int, int>> expected, actual;

        for (int v0 = v0_range.first; v0 <= v0_range.second; ++v0)
            for (int v1 = v1_range.first; v1 <= v1_range.second; ++v1)
                for (int v2 = v2_range.first; v2 <= v2_range.second; ++v2) {
                    bool ok = true;
                    for (auto & [linear, value] : constraints)
                        if (linear[0] * v0 + linear[1] * v1 + linear[2] * v2 > value) {
                            ok = false;
                            break;
                        }
                    if (ok)
                        expected.emplace(v0, v1, v2);
                }

        Problem p{Proof{"linear_equality_test.opb", "linear_equality_test.veripb"}};

        auto vs = vector{
            p.create_integer_range_variable(Integer{v0_range.first}, Integer{v0_range.second}),
            p.create_integer_range_variable(Integer{v1_range.first}, Integer{v1_range.second}),
            p.create_integer_range_variable(Integer{v2_range.first}, Integer{v2_range.second})};

        for (auto & [linear, value] : constraints) {
            Linear c;
            for_each_with_index(linear, [&](int coeff, auto idx) {
                if (coeff != 0)
                    c.emplace_back(Integer{coeff}, vs[idx]);
            });
            p.post(LinearLessEqual{move(c), Integer{value}});
        }

        solve(p, [&](const State & s) -> bool {
            actual.emplace(s(vs[0]).raw_value, s(vs[1]).raw_value, s(vs[2]).raw_value);
            return true;
        });

        if (! check_results(v0_range, v1_range, v2_range, constraints, "linear ineq", expected, actual))
            return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
