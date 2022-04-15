/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/min_max.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <util/enumerate.hh>

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
using std::cmp_less;
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
auto check_results(const Results_ & expected, const Results_ & actual) -> bool
{
    if (expected != actual) {
        cerr << " expected: " << expected.size() << endl;
        for (auto & [v, a] : expected) {
            cerr << "  " << v << " [";
            for (auto & v : a)
                cerr << " " << v;
            cerr << " ]" << endl;
        }
        cerr << "; actual: " << actual.size() << endl;
        for (auto & [v, a] : actual) {
            cerr << "  " << v << " [";
            for (auto & v : a)
                cerr << " " << v;
            cerr << " ]" << endl;
        }
        cerr << endl;

        return false;
    }
    cerr << endl;

    if (0 != system("veripb min_max_test.opb min_max_test.veripb"))
        return false;

    return true;
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

auto run_min_max_test(pair<int, int> result_range, const vector<pair<int, int>> & array_range) -> bool
{
    cerr << "MinMaxArray " << stringify_tuple(result_range) << " "
         << " [";
    for (const auto & v : array_range)
        cerr << " " << stringify_tuple(v);
    cerr << " ]";

    set<tuple<int, vector<int>>> expected, actual;
    {
        vector<int> array;
        grow(array, array_range, [&]() {
            auto min = *min_element(array.begin(), array.end());
            if (min >= result_range.first && min <= result_range.second)
                expected.emplace(min, array);
        });
    }

    Problem p{ProofOptions{"min_max_test.opb", "min_max_test.veripb"}};
    auto result = p.create_integer_variable(Integer(result_range.first), Integer(result_range.second), "result");
    vector<IntegerVariableID> array;
    for (const auto & [l, u] : array_range)
        array.push_back(p.create_integer_variable(Integer(l), Integer(u)));

    p.post(ArrayMin{array, result});
    bool gac_violated = false;
    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                vector<int> vals;
                for (auto & a : array)
                    vals.push_back(s(a).raw_value);
                actual.emplace(s(result).raw_value, vals);
                return true;
            },
            .trace = [&](const CurrentState & s) -> bool {
                s.for_each_value(result, [&](Integer val) {
                    bool violated = expected.end() == find_if(expected.begin(), expected.end(), [&](const auto & sol) {
                        if (Integer{get<0>(sol)} != val)
                            return false;
                        for (const auto & [idx, val] : enumerate(get<1>(sol)))
                            if (s.in_domain(array.at(idx), Integer{val}))
                                return true;
                        return false;
                    });
                    if (violated) {
                        cerr << "gac violated for result" << endl;
                        gac_violated = true;
                    }
                });

                for (const auto & [idx, var] : enumerate(array)) {
                    s.for_each_value(var, [&](Integer val) {
                        bool violated = expected.end() == find_if(expected.begin(), expected.end(), [&](const auto & sol) {
                            bool ok = true;
                            if (Integer{get<1>(sol).at(idx)} != val)
                                ok = false;
                            else if (! s.in_domain(result, Integer{get<0>(sol)}))
                                ok = false;
                            else
                                for (const auto & [idx, val] : enumerate(get<1>(sol)))
                                    if (! s.in_domain(array[idx], Integer{val}))
                                        ok = false;
                            return ok;
                        });
                        if (violated) {
                            cerr << "gac violated for var " << idx << " val " << val << ", result is [";
                            s.for_each_value(result, [&](Integer val) {
                                cerr << " " << val;
                            });
                            cerr << " ], vars are [";
                            for (auto & var : array) {
                                cerr << " [";
                                s.for_each_value(var, [&](Integer val) {
                                    cerr << " " << val;
                                });
                                cerr << " ]";
                            }
                            cerr << " ]" << endl;
                            gac_violated = true;
                        }
                    });
                }

                s.for_each_value(result, [&](Integer val) {
                    bool violated = expected.end() == find_if(expected.begin(), expected.end(), [&](const auto & sol) {
                        if (Integer{get<0>(sol)} != val)
                            return false;
                        for (const auto & [idx, val] : enumerate(get<1>(sol)))
                            if (s.in_domain(array.at(idx), Integer{val}))
                                return true;
                        return false;
                    });
                    if (violated) {
                        cerr << "gac violated for result" << endl;
                        gac_violated = true;
                    }
                });
                return true;
            }});

    return (! gac_violated) && check_results(expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, vector<pair<int, int>>>> data = {
        {{1, 2}, {{1, 2}, {1, 2}}},
        {{1, 2}, {{1, 2}, {1, 2}, {1, 2}}},
        {{0, 4}, {{1, 2}, {1, 2}, {1, 2}}},
        {{1, 3}, {{0, 4}, {0, 5}, {0, 6}}},
        {{-1, 3}, {{-1, 2}, {1, 3}, {4, 5}}},
        {{1, 4}, {{1, 4}, {2, 3}, {0, 5}, {-2, 0}, {5, 7}}},
        {{-5, 5}, {{-8, 0}, {4, 4}, {10, 10}, {2, 11}, {4, 10}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution result_lower_dist(-10, 10);
        auto result_lower = result_lower_dist(rand);
        uniform_int_distribution result_upper_dist(result_lower, result_lower + 10);
        auto result_upper = result_upper_dist(rand);

        vector<pair<int, int>> values;
        uniform_int_distribution n_values_dist(1, 5);
        auto n_values = n_values_dist(rand);
        for (int i = 0; i < n_values; ++i) {
            uniform_int_distribution val_lower_dist(-10, 10);
            auto val_lower = val_lower_dist(rand);
            uniform_int_distribution val_upper_dist(val_lower, val_lower + 10);
            auto val_upper = val_upper_dist(rand);
            values.emplace_back(val_lower, val_upper);
        }

        data.emplace_back(pair{result_lower, result_upper}, move(values));
    }

    for (auto & [r1, r2] : data) {
        if (! run_min_max_test(r1, r2))
            return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
