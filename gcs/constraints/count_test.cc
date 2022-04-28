/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/count.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
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

auto grow(vector<int> & array, const vector<pair<int, int>> & array_range, const function<void()> & yield) -> void
{
    if (array.size() == array_range.size())
        yield();
    else {
        for (int x = array_range[array.size()].first; x <= array_range[array.size()].second; ++x) {
            array.push_back(x);
            grow(array, array_range, yield);
            array.pop_back();
        }
    }
}

auto run_count_test(pair<int, int> result_range, pair<int, int> voi_range, const vector<pair<int, int>> & array_range) -> bool
{
    cerr << "Count " << stringify_tuple(result_range) << " " << stringify_tuple(voi_range) << " [";
    for (const auto & v : array_range)
        cerr << " " << stringify_tuple(v);
    cerr << " ]";

    set<tuple<int, int, vector<int>>> expected, actual;
    {
        vector<int> array;
        grow(array, array_range, [&]() {
            set<int> values{array.begin(), array.end()};
            for (int v = voi_range.first; v <= voi_range.second; ++v) {
                int result = count(array.begin(), array.end(), v);
                if (result >= result_range.first && result <= result_range.second)
                    expected.emplace(result, v, array);
            }
        });
    }

    cerr << " " << expected.size() << endl;

    Problem p{ProofOptions{"count_test.opb", "count_test.veripb"}};
    auto result = p.create_integer_variable(Integer(result_range.first), Integer(result_range.second), "result");
    auto voi = p.create_integer_variable(Integer(voi_range.first), Integer(voi_range.second), "voi");
    vector<IntegerVariableID> array;
    for (const auto & [l, u] : array_range)
        array.push_back(p.create_integer_variable(Integer(l), Integer(u)));

    p.post(Count{array, voi, result});
    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                vector<int> vals;
                for (auto & a : array)
                    vals.push_back(s(a).raw_value);
                actual.emplace(s(result).raw_value, s(voi).raw_value, vals);
                return true;
            }});

    if (actual != expected) {
        cerr << "actual:";
        for (auto & a : actual) {
            cerr << " (";
            auto & [r, h, v] = a;
            for (auto & vv : v)
                cerr << " " << vv;
            cerr << "), " << r << " " << h;
            if (! expected.contains(a))
                cerr << "!";
            cerr << ";";
        }
        cerr << " expected:";
        for (auto & a : expected) {
            cerr << " (";
            auto & [r, h, v] = a;
            for (auto & vv : v)
                cerr << " " << vv;
            cerr << "), " << r << " " << h;
            if (! actual.contains(a))
                cerr << "!";
            cerr << ";";
        }
        cerr << endl;

        return false;
    }

    if (0 != system("veripb count_test.opb count_test.veripb"))
        return false;

    return true;
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, vector<pair<int, int>>>> data = {
        {{1, 2}, {1, 2}, {{1, 2}, {1, 2}}},
        {{1, 2}, {0, 3}, {{1, 2}, {1, 2}}},
        {{1, 2}, {1, 2}, {{1, 2}, {1, 2}, {1, 2}}},
        {{0, 3}, {1, 2}, {{1, 2}, {1, 2}, {1, 2}}},
        {{0, 4}, {0, 4}, {{1, 2}, {1, 2}, {1, 2}}},
        {{1, 3}, {1, 6}, {{0, 4}, {0, 5}, {0, 6}}},
        {{-1, 3}, {0, 5}, {{-1, 2}, {1, 3}, {4, 5}}},
        {{1, 4}, {-3, 8}, {{1, 4}, {2, 3}, {0, 5}, {-2, 0}, {5, 7}}},
        {{0, 4}, {-5, 2}, {{7, 14}, {7, 11}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution result_lower_dist(-10, 10);
        auto result_lower = result_lower_dist(rand);
        uniform_int_distribution result_upper_dist(result_lower, result_lower + 10);
        auto result_upper = result_upper_dist(rand);

        uniform_int_distribution voi_lower_dist(-10, 10);
        auto voi_lower = voi_lower_dist(rand);
        uniform_int_distribution voi_upper_dist(voi_lower, voi_lower + 10);
        auto voi_upper = voi_upper_dist(rand);

        vector<pair<int, int>> values;
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values = n_values_dist(rand);
        for (int i = 0; i < n_values; ++i) {
            uniform_int_distribution val_lower_dist(-10, 10);
            auto val_lower = val_lower_dist(rand);
            uniform_int_distribution val_upper_dist(val_lower, val_lower + 10);
            auto val_upper = val_upper_dist(rand);
            values.emplace_back(val_lower, val_upper);
        }

        data.emplace_back(pair{result_lower, result_upper}, pair{voi_lower, voi_upper}, move(values));
    }

    for (auto & [r1, r2, r3] : data) {
        if (! run_count_test(r1, r2, r3))
            return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
