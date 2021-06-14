/* vim: set sw=4 sts=4 et foldmethod=syntax : */

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

    auto a = p.allocate_integer_variable(2_i, 8_i);
    auto b = p.allocate_integer_variable(3_i, 9_i);
    auto c = p.allocate_integer_offset_variable(b, 2_i);
    p.eq_reif(a, c, p.allocate_boolean_constant(true));

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << s.optional_single_value(a)->raw_value << " " << s.optional_single_value(b)->raw_value << " " << s.optional_single_value(c)->raw_value << endl;

            return true;
            });

    cout << "recursions: " << stats.recursions << endl;
    cout << "max depth:  " << stats.max_depth << endl;
    cout << "solve time: " << (stats.solve_time.count() / 1'000'000.0d) << "s" << endl;

    return EXIT_SUCCESS;
}

