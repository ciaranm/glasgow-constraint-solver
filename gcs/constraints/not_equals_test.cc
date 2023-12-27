#include <gcs/constraints/not_equals.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <random>
#include <set>
#include <string>
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

using namespace std::literals::string_literals;

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
auto check_results(pair<int, int> v1_range, pair<int, int> v2_range, const string & name, const Results_ & expected, const Results_ & actual) -> bool
{
    cerr << name << " " << stringify_tuple(v1_range) << " " << stringify_tuple(v2_range);
    if (expected != actual) {
        cerr << " expected:";
        for (auto & t : expected)
            cerr << " " << stringify_tuple(t);
        cerr << "; actual:";
        for (auto & t : actual)
            cerr << " " << stringify_tuple(t);
        cerr << endl;

        return false;
    }
    cerr << endl;

    if (0 != system("veripb equals_test.opb equals_test.veripb"))
        return false;

    return true;
}

auto check_gac_oneway(string direction, IntegerVariableID v1, IntegerVariableID v2, const CurrentState & s,
    const function<auto(int, int)->bool> & is_satisfing) -> bool
{
    bool ok = true;
    s.for_each_value(v1, [&](Integer val1) {
        bool found_support = false;
        s.for_each_value(v2, [&](Integer val2) {
            found_support = found_support || is_satisfing(val1.raw_value, val2.raw_value);
        });
        if (! found_support) {
            cerr << direction << " gac missing support: " << val1 << " from {";
            s.for_each_value(v2, [&](Integer val2) {
                cerr << " " << val2;
            });
            cerr << " }" << endl;
            ok = false;
        }
    });
    return ok;
}

template <typename Constraint_>
auto run_binary_equals_test(pair<int, int> v1_range, pair<int, int> v2_range, const function<auto(int, int)->bool> & is_satisfing) -> bool
{
    set<pair<int, int>> expected, actual;
    for (int v1 = v1_range.first; v1 <= v1_range.second; ++v1)
        for (int v2 = v2_range.first; v2 <= v2_range.second; ++v2)
            if (is_satisfing(v1, v2))
                expected.emplace(v1, v2);

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    p.post(Constraint_{v1, v2});
    bool gac_violated = false;
    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                actual.emplace(s(v1).raw_value, s(v2).raw_value);
                return true;
            },
            .trace = [&](const CurrentState & s) -> bool {
                gac_violated = gac_violated ||
                    ! check_gac_oneway(typeid(Constraint_).name() + " forward"s + " " + stringify_tuple(v1_range) + " " + stringify_tuple(v2_range), v1, v2, s, is_satisfing) ||
                    ! check_gac_oneway(typeid(Constraint_).name() + " reverse"s + " " + stringify_tuple(v1_range) + " " + stringify_tuple(v2_range), v2, v1, s, [&](int a, int b) { return is_satisfing(b, a); });
                return true;
            }},
        ProofOptions{"equals_test.opb", "equals_test.veripb"});

    return (! gac_violated) && check_results(v1_range, v2_range, typeid(Constraint_).name(), expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<pair<pair<int, int>, pair<int, int>>> data = {
        {{2, 5}, {1, 6}},
        {{1, 6}, {2, 5}},
        {{1, 3}, {1, 3}},
        {{1, 5}, {6, 8}},
        {{1, 1}, {2, 4}},
        {{-2, -2}, {-2, -1}}};

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

        data.emplace_back(pair{r1_lower, r1_upper}, pair{r2_lower, r2_upper});
    }

    for (auto & [r1, r2] : data) {
        if (! run_binary_equals_test<NotEquals>(r1, r2, [](int a, int b) { return a != b; }))
            return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
