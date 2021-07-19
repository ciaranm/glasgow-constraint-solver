/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/linear_equality.hh>
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

    auto s = p.create_integer_variable(1_i, 9_i);
    auto e = p.create_integer_variable(0_i, 9_i);
    auto n = p.create_integer_variable(0_i, 9_i);
    auto d = p.create_integer_variable(0_i, 9_i);
    auto m = p.create_integer_variable(1_i, 9_i);
    auto o = p.create_integer_variable(0_i, 9_i);
    auto r = p.create_integer_variable(0_i, 9_i);
    auto y = p.create_integer_variable(0_i, 9_i);

    vector<IntegerVariableID> vars{ s, e, n, d, m, o, r, y };
    p.post(AllDifferent{ vars });

    p.post(LinearEquality{ Linear{                  {  1000_i, s }, {  100_i, e }, {  10_i, n }, {  1_i, d },
                                                    {  1000_i, m }, {  100_i, o }, {  10_i, r }, {  1_i, e },
                                   { -10000_i, m }, { -1000_i, o }, { -100_i, n }, { -10_i, e }, { -1_i, y }, }, 0_i });

    auto stats = solve(p, [&] (const State & state) -> bool {
            cout << " " << state(s) << state(e) << state(n) << state(d) << endl;
            cout << " " << state(m) << state(o) << state(r) << state(e) << endl;
            cout << state(m) << state(o) << state(n)
                << state(e) << state(y) << endl;
            cout << endl;

            return true;
            });

    cout << stats;

    return EXIT_SUCCESS;
}

