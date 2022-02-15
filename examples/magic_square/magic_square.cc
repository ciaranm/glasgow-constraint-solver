/* vim : set sw = 4 sts = 4 et foldmethod = syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::ifstream;
using std::vector;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof")          //
        ("all-different", "Use AllDifferent rather than inequalities");

    po::options_description all_options{"All options"};
    all_options.add_options() //
        ("size", po::value<int>()->default_value(5), "Size of the problem to solve");

    all_options.add(display_options);

    po::positional_options_description positional_options;
    positional_options
        .add("size", -1);

    po::variables_map options_vars;

    try {
        po::store(po::command_line_parser(argc, argv)
                      .options(all_options)
                      .positional(positional_options)
                      .run(),
            options_vars);
        po::notify(options_vars);
    }
    catch (const po::error & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << "Usage: " << argv[0] << " [options] [size]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    cout << "Replicating the MiniCP Magic Square benchmark." << endl;
    cout << "See Laurent D. Michel, Pierre Schaus, Pascal Van Hentenryck:" << endl;
    cout << "\"MiniCP: a lightweight solver for constraint programming.\"" << endl;
    cout << "Math. Program. Comput. 13(1): 133-184 (2021)." << endl;
    cout << "This should take 6042079 recursions with default options." << endl;
    cout << endl;

    int size = options_vars["size"].as<int>();
    Problem p = options_vars.contains("prove") ? Problem{ProofOptions{"magic_square.opb", "magic_square.veripb"}} : Problem{};
    Integer m{size * (size * size + 1) / 2};

    vector<vector<IntegerVariableID>> grid;
    vector<IntegerVariableID> grid_flat;
    for (int x = 0; x < size; ++x) {
        grid.emplace_back();
        for (int y = 0; y < size; ++y) {
            auto var = p.create_integer_variable(1_i, Integer{size * size});
            grid[x].push_back(var);
            grid_flat.push_back(var);
        }
    }

    // As far as I can tell, the statistics reported in the paper only make
    // sense for non-GAC all-different.
    if (options_vars.contains("all-different")) {
        p.post(AllDifferent{grid_flat});
    }
    else {
        for (unsigned x = 0; x < grid_flat.size(); ++x)
            for (unsigned y = x + 1; y < grid_flat.size(); ++y)
                p.post(NotEquals{grid_flat[x], grid_flat[y]});
    }

    for (int x = 0; x < size; ++x) {
        Linear coeff_vars;
        for (int y = 0; y < size; ++y)
            coeff_vars.emplace_back(1_i, grid[x][y]);
        p.post(LinearEquality{move(coeff_vars), m});
    }

    for (int y = 0; y < size; ++y) {
        Linear coeff_vars;
        for (int x = 0; x < size; ++x)
            coeff_vars.emplace_back(1_i, grid[x][y]);
        p.post(LinearEquality{move(coeff_vars), m});
    }

    Linear coeff_vars1, coeff_vars2;
    for (int xy = 0; xy < size; ++xy) {
        coeff_vars1.emplace_back(1_i, grid[xy][xy]);
        coeff_vars2.emplace_back(1_i, grid[size - xy - 1][xy]);
    }
    p.post(LinearEquality{move(coeff_vars1), m});
    p.post(LinearEquality{move(coeff_vars2), m});

    p.post(LessThan{grid[0][size - 1], grid[size - 1][0]});
    p.post(LessThan{grid[0][0], grid[size - 1][size - 1]});
    p.post(LessThan{grid[0][0], grid[size - 1][0]});

    p.branch_on(grid_flat);

    unsigned long long n_solutions = 0;
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool {
                return ++n_solutions < 10000;
            },
            .guess = [&](const CurrentState & state, IntegerVariableID var) -> vector<Literal> {
                return vector<Literal>{var == state.lower_bound(var), var != state.lower_bound(var)};
            }});

    cout << stats;

    return EXIT_SUCCESS;
}
