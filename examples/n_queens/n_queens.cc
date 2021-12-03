/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <util/for_each.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <vector>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::to_string;
using std::vector;

auto main(int, char * []) -> int
{
    int size = 88;
    Problem p; //{ Proof{ "n_queens.opb", "n_queens.veripb" } };

    vector<SimpleIntegerVariableID> queens;
    for (int v = 0 ; v != size ; ++v)
        queens.push_back(p.create_integer_variable(0_i, Integer{ size - 1 }, "queen" + to_string(v)));

    for (int i = 0 ; i < size ; ++i) {
        for (int j = i + 1 ; j < size ; ++j) {
            p.post(NotEquals{ queens[i], queens[j] });
            p.post(NotEquals{ queens[i] + Integer{ j - i }, queens[j] });
            p.post(NotEquals{ queens[i] + -Integer{ j - i }, queens[j] });
        }
    }

    auto stats = solve_with(p, SolveCallbacks{
            .solution = [&] (const State & s) -> bool {
                cout << "solution:";
                for (auto & v : queens)
                    cout << " " << s(v);
                cout << endl;

                return false;
                },
            .guess = [&] (const State & state, IntegerVariableID var) -> vector<Literal> {
                return vector<Literal>{ var == state.lower_bound(var), var != state.lower_bound(var) };
            }
            });

    cout << stats;

    return EXIT_SUCCESS;
}

