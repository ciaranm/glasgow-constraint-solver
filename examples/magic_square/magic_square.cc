/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::ifstream;
using std::pair;
using std::stoi;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    int size = 5;

    if (argc > 2) {
        cerr << "Usage: " << argv[0] << " [ size ]" << endl;
        return EXIT_FAILURE;
    }

    if (argc >= 2)
        size = stoi(argv[1]);

    Problem p; // { Proof{ "magic_square.opb", "magic_square.veripb" } };
    Integer m{ size * (size * size + 1) / 2 };

    vector<vector<IntegerVariableID> > grid;
    vector<IntegerVariableID> grid_flat;
    for (int x = 0 ; x < size ; ++x) {
        grid.emplace_back();
        for (int y = 0 ; y < size ; ++y) {
            auto var = p.create_integer_variable(1_i, Integer{ size * size });
            grid[x].push_back(var);
            grid_flat.push_back(var);
        }
    }

    for (unsigned x = 0 ; x < grid_flat.size() ; ++x)
        for (unsigned y = x + 1 ; y < grid_flat.size() ; ++y)
            p.post(NotEquals{ grid_flat[x], grid_flat[y] });

//    p.post(AllDifferent{ grid_flat });

    for (int x = 0 ; x < size ; ++x) {
        Linear coeff_vars;
        for (int y = 0 ; y < size ; ++y)
            coeff_vars.emplace_back(1_i, grid[x][y]);
        p.post(LinearEquality{ move(coeff_vars), m });
    }

    for (int y = 0 ; y < size ; ++y) {
        Linear coeff_vars;
        for (int x = 0 ; x < size ; ++x)
            coeff_vars.emplace_back(1_i, grid[x][y]);
        p.post(LinearEquality{ move(coeff_vars), m });
    }

    Linear coeff_vars1, coeff_vars2;
    for (int xy = 0 ; xy < size ; ++xy) {
        coeff_vars1.emplace_back(1_i, grid[xy][xy]);
        coeff_vars2.emplace_back(1_i, grid[size - xy - 1][xy]);
    }
    p.post(LinearEquality{ move(coeff_vars1), m });
    p.post(LinearEquality{ move(coeff_vars2), m });

    p.post(LessThan{ grid[0][size - 1], grid[size - 1][0] });
    p.post(LessThan{ grid[0][0], grid[size - 1][size - 1] });
    p.post(LessThan{ grid[0][0], grid[size - 1][0] });

    p.branch_on(grid_flat);

    unsigned long long n_solutions = 0;
    auto stats = solve_with(p, SolveCallbacks{
            .solution = [&] (const State &) -> bool {
                return ++n_solutions < 10000;
            },
            .guess = [&] (const State & state, IntegerVariableID var) -> vector<Literal> {
                return vector<Literal>{ var == state.lower_bound(var), var != state.lower_bound(var) };
            }
            } );

    cout << stats;

    return EXIT_SUCCESS;
}

