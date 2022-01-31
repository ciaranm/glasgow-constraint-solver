/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <vector>

using namespace gcs;

using std::cout;
using std::endl;
using std::vector;

auto main(int, char *[]) -> int
{
    Problem p{Proof{"triangle.opb", "triangle.veripb"}};
    auto [a, b, c] = p.create_n_integer_variables<3>(1_i, 10_i);
    auto [a_squared, b_squared, c_squared] = p.create_n_integer_variables<3>(1_i, 100_i);
    p.branch_on(vector<IntegerVariableID>{a, b, c});

    p.post(Power{a, constant_variable(2_i), a_squared});
    p.post(Power{b, constant_variable(2_i), b_squared});
    p.post(Power{c, constant_variable(2_i), c_squared});
    p.post(Plus{a_squared, b_squared, c_squared});
    p.post(LessThan{a, b});

    auto stats = solve(p, [&, a = a, b = b, c = c](const State & state) -> bool {
        cout << state(a) << " " << state(b) << " " << state(c) << endl;
        return true;
    });

    cout << stats;

    return EXIT_SUCCESS;
}
