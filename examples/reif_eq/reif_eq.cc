/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>

using namespace gcs;

using std::cout;
using std::endl;

auto main(int, char * []) -> int
{
    Problem p;

    auto a = p.create_integer_variable(2_i, 8_i);
    auto b = p.create_integer_variable(3_i, 9_i);
    auto c = p.create_integer_variable(5_i, 11_i);
    p.post(Plus{ b, p.create_integer_constant(2_i), c });
    p.post(Equals{ a, c });

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << s(a) << " " << s(b) << " " << s(c) << endl;

            return true;
            });

    cout << stats;

    return EXIT_SUCCESS;
}

