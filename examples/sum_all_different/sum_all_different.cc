/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <vector>

using namespace gcs;

using std::cout;
using std::endl;

auto main(int, char *[]) -> int
{
    Problem p{ProofOptions{"sum_all_different.opb", "sum_all_different.veripb"}};

    auto xs = p.create_integer_variable_vector(4, 1_i, 5_i, "xs");
    for (auto & x : xs)
        p.post(NotEquals(x, 3_c));

    p.post(AllDifferent{xs});

    Linear sum_xs;
    for (auto & x : xs)
        sum_xs.emplace_back(1_i, x);
    p.post(LinearEquality{move(sum_xs), 14_i, true});

    auto stats = solve(p, [&](const CurrentState & s) -> bool {
        cout << "[";
        for (auto & x : xs)
            cout << " " << s(x);
        cout << " ]" << endl;

        return true;
    });

    cout << stats;

    return EXIT_SUCCESS;
}
