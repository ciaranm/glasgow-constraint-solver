/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/element.hh>
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
    int k = 7;

    Problem p{ProofOptions{"langford.opb", "langford.veripb"}};
    vector<IntegerVariableID> position, solution;
    for (int i = 0; i < 2 * k; ++i) {
        position.emplace_back(p.create_integer_variable(0_i, Integer{2 * k - 1}));
        solution.emplace_back(p.create_integer_variable(1_i, Integer{k}));
    }

    p.post(AllDifferent{position});

    for (int i = 0; i < k; ++i) {
        auto i_var = p.create_integer_variable(Integer{i + 1}, Integer{i + 1});
        p.post(Element{i_var, position[i], solution});
        p.post(Element{i_var, position[i + k], solution});

        // position[i + k] = position[i] + i + 2
        p.post(Plus{position[i + k], constant_variable(Integer{i + 2}), position[i]});
    }

    auto stats = solve(p, [&](const CurrentState & state) -> bool {
        cout << "solution: ";
        for (auto & s : solution)
            cout << state(s) << " ";
        cout << endl;
        cout << "position: ";
        for (auto & s : position)
            cout << state(s) << " ";
        cout << endl;
        cout << endl;

        return true;
    });

    cout << stats;

    return EXIT_SUCCESS;
}
