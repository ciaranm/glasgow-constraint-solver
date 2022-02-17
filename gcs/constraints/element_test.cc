/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/element.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <util/for_each.hh>

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
        for (auto & [v, i, a] : expected) {
            cerr << "  " << v << " " << i << " [";
            for (auto & v : a)
                cerr << " " << v;
            cerr << " ]" << endl;
        }
        cerr << "; actual: " << actual.size() << endl;
        for (auto & [v, i, a] : actual) {
            cerr << "  " << v << " " << i << " [";
            for (auto & v : a)
                cerr << " " << v;
            cerr << " ]" << endl;
        }
        cerr << endl;

        return false;
    }
    cerr << endl;

    if (0 != system("veripb element_test.opb element_test.veripb"))
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

auto check_idx_gac(IntegerVariableID var, IntegerVariableID idx, const vector<IntegerVariableID> & vars, const CurrentState & s) -> bool
{
    bool ok = true;
    s.for_each_value(idx, [&](Integer idx_val) {
        bool found_support = false;
        s.for_each_value(var, [&](Integer val) {
            found_support = found_support || s.in_domain(vars[idx_val.raw_value], val);
        });

        if (! found_support) {
            cerr << "idx missing support: " << idx_val << endl;
            ok = false;
        }
    });
    return ok;
}

auto check_var_gac(IntegerVariableID var, IntegerVariableID idx, const vector<IntegerVariableID> & vars, const CurrentState & s) -> bool
{
    bool ok = true;
    s.for_each_value(var, [&](Integer var_val) {
        bool found_support = false;
        s.for_each_value(idx, [&](Integer idx_val) {
            found_support = found_support || s.in_domain(vars[idx_val.raw_value], var_val);
        });

        if (! found_support) {
            cerr << "var missing support: " << var_val << endl;
            ok = false;
        }
    });
    return ok;
}

auto check_vals_gac(IntegerVariableID var, IntegerVariableID idx, const vector<IntegerVariableID> & vars, const CurrentState & s) -> bool
{
    bool ok = true;
    for_each_with_index(vars, [&](IntegerVariableID avar, auto index) {
        if (s.has_single_value(idx) && s(idx) == Integer(index)) {
            s.for_each_value(avar, [&](Integer aval) {
                if (! s.in_domain(var, aval)) {
                    cerr << "avar " << index << " missing support: " << aval << " when idx is " << s(idx)
                         << ", var is ";
                    s.for_each_value(var, [&](Integer v) {
                        cerr << " " << v;
                    });
                    cerr << ", all vars are [ ";
                    for (auto & v : vars) {
                        cerr << "[";
                        s.for_each_value(v, [&](Integer val) {
                            cerr << " " << val;
                        });
                        cerr << " ]";
                    }
                    cerr << " ]" << endl;
                    ok = false;
                }
            });
        }
    });
    return ok;
}

auto run_element_test(pair<int, int> var_range, pair<int, int> idx_range, const vector<pair<int, int>> & array_range) -> bool
{
    cerr << "Element " << stringify_tuple(var_range) << " " << stringify_tuple(idx_range) << " [";
    for (const auto & v : array_range)
        cerr << " " << stringify_tuple(v);
    cerr << " ]";

    set<tuple<int, int, vector<int>>> expected, actual;
    for (int var = var_range.first; var <= var_range.second; ++var)
        for (int idx = idx_range.first; idx <= idx_range.second; ++idx) {
            vector<int> array;
            grow(array, array_range, [&]() {
                if (idx >= 0 && cmp_less(idx, array.size()) && array[idx] == var)
                    expected.emplace(var, idx, array);
            });
        }

    Problem p{ProofOptions{"element_test.opb", "element_test.veripb"}};
    auto var = p.create_integer_variable(Integer(var_range.first), Integer(var_range.second), "var");
    auto idx = p.create_integer_variable(Integer(idx_range.first), Integer(idx_range.second), "idx");
    vector<IntegerVariableID> array;
    for (const auto & [l, u] : array_range)
        array.push_back(p.create_integer_variable(Integer(l), Integer(u)));

    p.post(Element{var, idx, array});
    bool gac_violated = false;
    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                vector<int> vals;
                for (auto & a : array)
                    vals.push_back(s(a).raw_value);
                actual.emplace(s(var).raw_value, s(idx).raw_value, vals);
                return true;
            },
            .trace = [&](const CurrentState & s) -> bool {
                gac_violated = gac_violated || ! check_idx_gac(var, idx, array, s) ||
                    ! check_var_gac(var, idx, array, s) || ! check_vals_gac(var, idx, array, s);
                return true;
            }});

    return (! gac_violated) && check_results(expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, vector<pair<int, int>>>> data = {
        {{1, 2}, {0, 1}, {{1, 2}, {1, 2}}},
        {{1, 2}, {-2, 2}, {{1, 2}, {1, 2}}},
        {{1, 2}, {0, 1}, {{1, 2}, {1, 2}, {1, 2}}},
        {{-1, 3}, {0, 2}, {{-1, 2}, {1, 3}, {4, 5}}},
        {{1, 4}, {0, 4}, {{1, 4}, {2, 3}, {0, 5}, {-2, 0}, {5, 7}}},
        {{-5, 5}, {-3, 2}, {{-8, 0}, {4, 4}, {10, 10}, {2, 11}, {4, 10}}},
        {{7, 10}, {0, 9}, {{8, 18}, {9, 19}, {-1, 0}, {-6, 0}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution var_lower_dist(-10, 10);
        auto var_lower = var_lower_dist(rand);
        uniform_int_distribution var_upper_dist(var_lower, var_lower + 10);
        auto var_upper = var_upper_dist(rand);

        uniform_int_distribution idx_lower_dist(-3, 10);
        auto idx_lower = idx_lower_dist(rand);
        uniform_int_distribution idx_upper_dist(idx_lower, idx_lower + 10);
        auto idx_upper = idx_upper_dist(rand);

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

        data.emplace_back(pair{var_lower, var_upper}, pair{idx_lower, idx_upper}, move(values));
    }

    for (auto & [r1, r2, r3] : data) {
        if (! run_element_test(r1, r2, r3))
            return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
