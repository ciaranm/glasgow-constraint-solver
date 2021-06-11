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

    vector<IntegerVariableID> xs;
    xs.push_back(p.allocate_integer_variable(1_i, 5_i));
    xs.push_back(p.allocate_integer_variable(1_i, 5_i));
    xs.push_back(p.allocate_integer_variable(1_i, 5_i));
    xs.push_back(p.allocate_integer_variable(1_i, 5_i));

    for (auto & x : xs)
        p.cnf({ x != 3_i });

    p.all_different(xs);

    Linear sum_xs;
    for (auto & x : xs)
        sum_xs.emplace_back(1_i, x);
    p.lin_eq(move(sum_xs), 14_i);

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << "[";
            for (auto & x : xs)
                cout << " " << s.value_of(x)->raw_value;
            cout << " ]" << endl;

            return true;
            });

    cout << "recursions: " << stats.recursions << endl;
    cout << "max depth:  " << stats.max_depth << endl;

    return EXIT_SUCCESS;
}

