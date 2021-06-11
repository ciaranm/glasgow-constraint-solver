/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <vector>

using namespace gcs;

using std::cout;
using std::endl;
using std::pair;
using std::vector;

auto main(int, char * []) -> int
{
    Problem p;

    auto s = p.allocate_integer_variable(9_i, 9_i);
    auto e = p.allocate_integer_variable(5_i, 5_i);
    auto n = p.allocate_integer_variable(6_i, 6_i);
    auto d = p.allocate_integer_variable(0_i, 9_i);
    auto m = p.allocate_integer_variable(1_i, 9_i);
    auto o = p.allocate_integer_variable(0_i, 9_i);
    auto r = p.allocate_integer_variable(0_i, 9_i);
    auto y = p.allocate_integer_variable(0_i, 9_i);

    vector<IntegerVariableID> vars{ s, e, n, d, m, o, r, y };
    p.all_different(vars);

    auto r1 = p.allocate_integer_variable(0_i, 9999_i);
    auto r2 = p.allocate_integer_variable(0_i, 9999_i);
    auto r3 = p.allocate_integer_variable(10000_i, 19999_i);
    p.lin_eq(vector<pair<Integer, IntegerVariableID> >{                     pair{ 1000_i, s }, pair{ 100_i, e }, pair{ 10_i, n }, pair{ 1_i, d }, pair{ -1_i, r1 } }, 0_i);
    p.lin_eq(vector<pair<Integer, IntegerVariableID> >{                     pair{ 1000_i, m }, pair{ 100_i, o }, pair{ 10_i, r }, pair{ 1_i, e }, pair{ -1_i, r2 } }, 0_i);
    p.lin_eq(vector<pair<Integer, IntegerVariableID> >{ pair{ 10000_i, m }, pair{ 1000_i, o }, pair{ 100_i, n }, pair{ 10_i, e }, pair{ 1_i, y }, pair{ -1_i, r3 } }, 0_i);

    p.lin_eq(vector<pair<Integer, IntegerVariableID> >{ pair{ 1_i, r1 }, pair{ 1_i, r2 }, pair{ -1_i, r3 } }, 0_i);

    auto stats = solve(p, [&] (const State & state) -> bool {
            cout << " " << state.value_of(s)->raw_value << state.value_of(e)->raw_value << state.value_of(n)->raw_value << state.value_of(d)->raw_value << endl;
            cout << " " << state.value_of(m)->raw_value << state.value_of(o)->raw_value << state.value_of(r)->raw_value << state.value_of(e)->raw_value << endl;
            cout << state.value_of(m)->raw_value << state.value_of(o)->raw_value << state.value_of(n)->raw_value << state.value_of(e)->raw_value << state.value_of(y)->raw_value << endl;
            cout << endl;

            return true;
            });

    cout << "recursions: " << stats.recursions << endl;
    cout << "max depth:  " << stats.max_depth << endl;

    return EXIT_SUCCESS;
}

