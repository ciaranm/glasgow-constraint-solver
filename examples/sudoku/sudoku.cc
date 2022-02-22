/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <utility>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::vector;

namespace po = boost::program_options;

using namespace std::literals::string_literals;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");

    po::options_description all_options{"All options"};
    all_options.add_options() //
        ("all", "Find all solutions");

    all_options.add(display_options);

    po::variables_map options_vars;

    try {
        po::store(po::command_line_parser(argc, argv)
                      .options(all_options)
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
        cout << "Usage: " << argv[0] << " [options]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    Problem p = options_vars.contains("prove") ? Problem{ProofOptions{"sudoku.opb", "sudoku.veripb"}} : Problem{};

    int size = 3;
    int n = size * size;

    // https://www.minizinc.org/doc-2.5.5/en/modelling2.html#conditional-expressions
    vector<vector<int> > predef = {
        {0, 0, 0, 0, 0, 0, 0, 0, 0},
        {0, 6, 8, 4, 0, 1, 0, 7, 0},
        {0, 0, 0, 0, 8, 5, 0, 3, 0},
        {0, 2, 6, 8, 0, 9, 0, 4, 0},
        {0, 0, 7, 0, 0, 0, 9, 0, 0},
        {0, 5, 0, 1, 0, 6, 3, 2, 0},
        {0, 4, 0, 6, 1, 0, 0, 0, 0},
        {0, 3, 0, 2, 0, 7, 6, 9, 0},
        {0, 0, 0, 0, 0, 0, 0, 0, 0}
    };

    vector<vector<IntegerVariableID>> grid;

    for (int r = 0; r < n; ++r)
        grid.emplace_back(p.create_integer_variable_vector(n, 1_i, Integer{n}, "grid"));

    for (int r = 0; r < n; ++r)
        p.post(AllDifferent{grid[r]});

    for (int c = 0; c < n; ++c) {
        vector<IntegerVariableID> column;
        for (int r = 0; r < n; ++r)
            column.push_back(grid[r][c]);
        p.post(AllDifferent{column});
    }

    for (int r = 0; r < size; ++r)
        for (int c = 0; c < size; ++c)
        {
            vector<IntegerVariableID> box;
            for (int rr = 0; rr < size; ++rr)
                for (int cc = 0; cc < size; ++cc)
                    box.push_back(grid[r * size + rr][c * size + cc]);
            p.post(AllDifferent{box});
        }

    for (int r = 0; r < n; ++r)
        for (int c = 0; c < n; ++c)
            if (predef[r][c] != 0)
                p.post(Equals{grid[r][c], constant_variable(Integer{predef[r][c]})});

    auto stats = solve(p, [&](const CurrentState & s) -> bool {
        for (const auto & row : grid) {
            bool first = true;
            for (const auto & box : row) {
                if (! first)
                    cout << " ";
                cout << s(box);
                first = false;
            }
            cout << endl;
        }
        cout << endl;
        return options_vars.contains("all");
    });

    cout << stats;

    return EXIT_SUCCESS;
}

