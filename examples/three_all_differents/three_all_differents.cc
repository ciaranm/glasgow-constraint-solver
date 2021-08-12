/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
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
    Problem p{ Proof{ "three_all_differents.opb", "three_all_differents.veripb" } };

    IntegerVariableID w = p.create_integer_variable(0_i, 1_i);
    IntegerVariableID x = p.create_integer_variable(1_i, 2_i);
    IntegerVariableID y = p.create_integer_variable(0_i, 2_i);
    IntegerVariableID z = p.create_integer_variable(0_i, 1_i);
    p.post(AllDifferent{ { w, x, y } });
    p.post(AllDifferent{ { x, y, z } });
    p.post(AllDifferent{ { w, z } });

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << s(w) << " " << s(x) << " " << s(y) << " " << s(z) << endl;
            return true;
            });

    cout << stats;

    return EXIT_SUCCESS;
}
