/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/problem.hh>
#include <gcs/constraints/element.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <set>
#include <tuple>
#include <vector>
#include <utility>

using std::cerr;
using std::cmp_less;
using std::endl;
using std::function;
using std::index_sequence;
using std::make_index_sequence;
using std::pair;
using std::set;
using std::string;
using std::to_string;
using std::tuple;
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
auto check_results(pair<int, int> var_range, pair<int, int> idx_range, const Results_ & expected, const Results_ & actual) -> bool
{
    cerr << "Element " << stringify_tuple(var_range) << " " << stringify_tuple(idx_range);
    if (expected != actual) {
        cerr << " expected: " << expected.size() << endl;
        for (auto & [ v, i, a ] : expected) {
            cerr << "  " << v << " " << i << " [";
            for (auto & v : a)
                cerr << " " << v;
            cerr << " ]" << endl;
        }
        cerr << "; actual: " << actual.size() << endl;
        for (auto & [ v, i, a ] : actual) {
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

auto grow(vector<int> & array, const vector<pair<int, int> > & array_range, const function<void ()> & yield) -> void
{
    if (array.size() == array_range.size())
        yield();
    else {
        for (int x = array_range[array.size()].first ; x <= array_range[array.size()].second ; ++x) {
            array.push_back(x);
            grow(array, array_range, yield);
            array.pop_back();
        }
    }
}

auto run_element_test(pair<int, int> var_range, pair<int, int> idx_range, const vector<pair<int, int> > & array_range) -> bool
{
    set<tuple<int, int, vector<int> > > expected, actual;
    for (int var = var_range.first ; var <= var_range.second ; ++var)
        for (int idx = idx_range.first ; idx <= idx_range.second ; ++idx)
        {
            vector<int> array;
            grow(array, array_range, [&] () {
                    if (idx >= 0 && cmp_less(idx, array.size()) && array[idx] == var)
                        expected.emplace(var, idx, array);
                    } );
        }

    Problem p{ Proof{ "element_test.opb", "element_test.veripb" } };
    auto var = p.create_integer_variable(Integer(var_range.first), Integer(var_range.second));
    auto idx = p.create_integer_variable(Integer(idx_range.first), Integer(idx_range.second));
    vector<IntegerVariableID> array;
    for (auto & [ l, u ] : array_range)
        array.push_back(p.create_integer_variable(Integer(l), Integer(u)));

    p.post(Element{ var, idx, array });
    solve(p, [&] (const State & s) -> bool {
            vector<int> vals;
            for (auto & a : array)
                vals.push_back(s(a).raw_value);
            actual.emplace(s(var).raw_value, s(idx).raw_value, vals);
            return true;
            });

    return check_results(var_range, idx_range, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, vector<pair<int, int> > > > data = {
        { { 1, 2 }, { 0, 1 }, { { 1, 2 }, { 1, 2 } } },
        { { 1, 2 }, { -2, 2 }, { { 1, 2 }, { 1, 2 } } },
        { { 1, 2 }, { 0, 1 }, { { 1, 2 }, { 1, 2 }, { 1, 2 } } },
        { { -1, 3 }, { 0, 2 }, { { -1, 2 }, { 1, 3 }, { 4, 5 } } },
        { { 1, 4 }, { 0, 4 }, { { 1, 4 }, { 2, 3 }, { 0, 5 }, { -2, 0 }, { 5, 7 } } }
    };


    for (auto & [ r1, r2, r3 ] : data) {
        if (! run_element_test(r1, r2, r3))
            return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}

