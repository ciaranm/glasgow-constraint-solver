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
    int k = 7;

    Problem p;
    vector<IntegerVariableID> position, solution;
    for (int i = 0 ; i < 2 * k ; ++i) {
        position.push_back(p.allocate_integer_variable(0_i, Integer{ 2 * k - 1 }));
        solution.push_back(p.allocate_integer_variable(1_i, Integer{ k }));
    }

    p.all_different(position);

    for (int i = 0 ; i < k ; ++i) {
        auto i_var = p.allocate_integer_variable(Integer{ i + 1 }, Integer{ i + 1 });
        p.element(i_var, position[i], solution);
        p.element(i_var, position[i + k], solution);
        p.lin_eq(Linear{ { 1_i, position[i + k] }, { -1_i, position[i] } }, Integer{ i + 2 });
    }

    auto stats = solve(p, [&] (const State & state) -> bool {
            cout << "solution: ";
            for (auto & s : solution)
                cout << state.value_of(s)->raw_value << " ";
            cout << endl;
            cout << "position: ";
            for (auto & s : position)
                cout << state.value_of(s)->raw_value << " ";
            cout << endl;
            cout << endl;

            return true;
            });

    cout << "recursions: " << stats.recursions << endl;
    cout << "max depth:  " << stats.max_depth << endl;
    cout << "solutions: "  << stats.solutions << endl;
    cout << "solve time: " << (stats.solve_time.count() / 1'000'000.0d) << "s" << endl;

    return EXIT_SUCCESS;
}


