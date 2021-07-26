/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/constraints/equals.hh>
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
    xs.push_back(p.create_integer_variable(1_i, 5_i));
    xs.push_back(p.create_integer_variable(1_i, 5_i));
    xs.push_back(p.create_integer_variable(1_i, 5_i));
    xs.push_back(p.create_integer_variable(1_i, 5_i));

    auto three = p.create_integer_constant(3_i);
    for (auto & x : xs)
        p.post(NotEquals(x, three ));

    p.post(AllDifferent{ move(xs) });

    Linear sum_xs;
    for (auto & x : xs)
        sum_xs.emplace_back(1_i, x);
    p.post(LinearEquality{ move(sum_xs), 14_i });

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << "[";
            for (auto & x : xs)
                cout << " " << s(x);
            cout << " ]" << endl;

            return true;
            });

    cout << stats;

    return EXIT_SUCCESS;
}

