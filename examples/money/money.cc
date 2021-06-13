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

    auto s = p.allocate_integer_variable(1_i, 9_i);
    auto e = p.allocate_integer_variable(0_i, 9_i);
    auto n = p.allocate_integer_variable(0_i, 9_i);
    auto d = p.allocate_integer_variable(0_i, 9_i);
    auto m = p.allocate_integer_variable(1_i, 9_i);
    auto o = p.allocate_integer_variable(0_i, 9_i);
    auto r = p.allocate_integer_variable(0_i, 9_i);
    auto y = p.allocate_integer_variable(0_i, 9_i);

    vector<IntegerVariableID> vars{ s, e, n, d, m, o, r, y };
    p.all_different(vars);

    p.lin_eq(Linear{                 {  1000_i, s }, {  100_i, e }, {  10_i, n }, {  1_i, d },
                                     {  1000_i, m }, {  100_i, o }, {  10_i, r }, {  1_i, e },
                    { -10000_i, m }, { -1000_i, o }, { -100_i, n }, { -10_i, e }, { -1_i, y }, }, 0_i);

    auto stats = solve(p, [&] (const State & state) -> bool {
            cout << " " << state.value_of(s)->raw_value << state.value_of(e)->raw_value << state.value_of(n)->raw_value << state.value_of(d)->raw_value << endl;
            cout << " " << state.value_of(m)->raw_value << state.value_of(o)->raw_value << state.value_of(r)->raw_value << state.value_of(e)->raw_value << endl;
            cout << state.value_of(m)->raw_value << state.value_of(o)->raw_value << state.value_of(n)->raw_value << state.value_of(e)->raw_value << state.value_of(y)->raw_value << endl;
            cout << endl;

            return true;
            });

    cout << "recursions: " << stats.recursions << endl;
    cout << "max depth:  " << stats.max_depth << endl;
    cout << "solve time: " << (stats.solve_time.count() / 1'000'000.0d) << "s" << endl;

    return EXIT_SUCCESS;
}

