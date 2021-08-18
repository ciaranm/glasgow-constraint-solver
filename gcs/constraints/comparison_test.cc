/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/problem.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <set>
#include <tuple>
#include <vector>
#include <utility>

using std::cerr;
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
auto check_results(const Results_ & expected, const Results_ & actual) -> bool
{
    if (expected != actual) {
        cerr << "expected:";
        for (auto & t : expected)
            cerr << " " << stringify_tuple(t);
        cerr << endl;
        cerr << "actual:";
        for (auto & t : actual)
            cerr << " " << stringify_tuple(t);
        cerr << endl;

        return false;
    }

    if (0 != system("veripb comparison_test.opb comparison_test.veripb"))
        return false;

    return true;
}

template <typename Constraint_>
auto run_binary_comparison_test(pair<int, int> v1_range, pair<int, int> v2_range, const function<auto (int, int) -> bool> & is_satisfing) -> bool
{
    set<pair<int, int> > expected, actual;
    for (int v1 = v1_range.first ; v1 <= v1_range.second ; ++v1)
        for (int v2 = v2_range.first ; v2 <= v2_range.second ; ++v2)
            if (is_satisfing(v1, v2))
                expected.emplace(v1, v2);

    Problem p{ Proof{ "comparison_test.opb", "comparison_test.veripb" } };
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    p.post(Constraint_{ v1, v2 });
    solve(p, [&] (const State & s) -> bool {
            actual.emplace(s(v1).raw_value, s(v2).raw_value);
            return true;
            });

    return check_results(expected, actual);
}

template <typename Constraint_>
auto run_reif_binary_comparison_test(pair<int, int> v1_range, pair<int, int> v2_range, const function<auto (int, int) -> bool> & is_satisfing) -> bool
{
    set<tuple<int, int, int> > expected, actual;
    for (int v1 = v1_range.first ; v1 <= v1_range.second ; ++v1)
        for (int v2 = v2_range.first ; v2 <= v2_range.second ; ++v2)
            expected.emplace(v1, v2, is_satisfing(v1, v2));

    Problem p{ Proof{ "comparison_test.opb", "comparison_test.veripb" } };
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    auto v3 = p.create_integer_variable(0_i, 1_i);
    p.post(Constraint_{ v1, v2, v3 == 1_i });
    solve(p, [&] (const State & s) -> bool {
            actual.emplace(s(v1).raw_value, s(v2).raw_value, s(v3).raw_value);
            return true;
            });

    return check_results(expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<pair<pair<int, int>, pair<int, int> > > data = {
        { { 2, 5 }, { 1, 6 } },
        { { 1, 6 }, { 2, 5 } },
        { { 1, 3 }, { 1, 3 } },
        { { 1, 5 }, { 6, 8 } },
        { { 1, 1 }, { 2, 4 } }
    };

    for (auto & [ r1, r2 ] : data) {
        if (! run_binary_comparison_test<Equals>(r1, r2, [] (int a, int b) { return a == b; }))
            return EXIT_FAILURE;
        if (! run_binary_comparison_test<NotEquals>(r1, r2, [] (int a, int b) { return a != b; }))
            return EXIT_FAILURE;
        if (! run_reif_binary_comparison_test<EqualsIff>(r1, r2, [] (int a, int b) { return a == b; }))
            return EXIT_FAILURE;
        if (! run_reif_binary_comparison_test<NotEqualsIff>(r1, r2, [] (int a, int b) { return a != b; }))
            return EXIT_FAILURE;

        if (! run_binary_comparison_test<LessThan>(r1, r2, [] (int a, int b) { return a < b; }))
            return EXIT_FAILURE;
        if (! run_binary_comparison_test<LessThanEqual>(r1, r2, [] (int a, int b) { return a <= b; }))
            return EXIT_FAILURE;
        if (! run_binary_comparison_test<GreaterThan>(r1, r2, [] (int a, int b) { return a > b; }))
            return EXIT_FAILURE;
        if (! run_binary_comparison_test<GreaterThanEqual>(r1, r2, [] (int a, int b) { return a >= b; }))
            return EXIT_FAILURE;

        if (! run_reif_binary_comparison_test<LessThanIff>(r1, r2, [] (int a, int b) { return a < b; }))
            return EXIT_FAILURE;
        if (! run_reif_binary_comparison_test<LessThanEqualIff>(r1, r2, [] (int a, int b) { return a <= b; }))
            return EXIT_FAILURE;
        if (! run_reif_binary_comparison_test<GreaterThanIff>(r1, r2, [] (int a, int b) { return a > b; }))
            return EXIT_FAILURE;
        if (! run_reif_binary_comparison_test<GreaterThanEqualIff>(r1, r2, [] (int a, int b) { return a >= b; }))
            return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}

