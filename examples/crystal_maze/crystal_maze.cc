/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/abs.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <vector>

using namespace gcs;

using std::cout;
using std::endl;
using std::to_string;
using std::pair;
using std::vector;

auto main(int, char * []) -> int
{
    Problem p{ Proof{ "crystal_maze.opb", "crystal_maze.veripb" } };

    vector<IntegerVariableID> xs;
    for (int i = 0 ; i < 8 ; ++i)
        xs.push_back(p.create_integer_variable(1_i, 8_i, "box" + to_string(i)));

    p.post(AllDifferent{ xs });
    p.branch_on(xs);

    vector<pair<int, int> > edges{ { 0, 1 }, { 0, 2 }, { 0, 3 }, { 0, 4 },
        { 1, 3 }, { 1, 4 }, { 1, 5 }, { 2, 3 }, { 2, 6 }, { 3, 4 }, { 3, 6 },
        { 3, 7 }, { 4, 5 }, { 4, 6 }, { 4, 7 }, { 5, 7 }, { 6, 7 } };

    bool use_abs = false;
    vector<IntegerVariableID> diffs, abs_diffs;
    for (auto & [ x1, x2 ] : edges) {
        diffs.push_back(p.create_integer_variable(-7_i, 7_i, "diff" + to_string(x1) + "_" + to_string(x2)));
        if (use_abs) {
            abs_diffs.push_back(p.create_integer_variable(2_i, 7_i, "absdiff" + to_string(x1) + "_" + to_string(x2)));
            p.post(Abs{ diffs.back(), abs_diffs.back() });
        }
        else {
            p.post(NotEquals{ diffs.back(), constant_variable(0_i) });
            p.post(NotEquals{ diffs.back(), constant_variable(1_i) });
            p.post(NotEquals{ diffs.back(), constant_variable(-1_i) });
        }

        p.post(Minus{ xs[x1], xs[x2], diffs.back() });
    }

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << "  " << s(xs[0]) << " " << s(xs[1]) << endl;
            cout << s(xs[2]) << " " << s(xs[3]) << " " << s(xs[4]) << " " << s(xs[5]) << endl;
            cout << "  " << s(xs[6]) << " " << s(xs[7]) << endl;
            cout << endl;
            return true;
            });

    cout << stats;

    return EXIT_SUCCESS;
}

