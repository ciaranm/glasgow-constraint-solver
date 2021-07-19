/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/equals_reif.hh>
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
    auto c = p.create_integer_offset_variable(b, 2_i);
    p.post(EqualsReif{ a, c, p.create_boolean_constant(true) });

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << s(a) << " " << s(b) << " " << s(c) << endl;

            return true;
            });

    cout << stats;

    return EXIT_SUCCESS;
}

