#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear_equality.hh>
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
using std::make_optional;
using std::nullopt;
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
    all_options.add_options()                 //
        ("xv", "Solve the xv puzzle instead") //
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

    Problem p;

    int size = 3;
    int n = size * size;

    enum NXV
    {
        N, // no v or x rule
        V, // must sum to 5
        X, // must sum to 10
        O  // must not sum to 5 or 10
    };

    vector<vector<int>> predef;
    vector<vector<NXV>> horizontal_xvs, vertical_xvs;

    if (options_vars.contains("xv")) {
        // https://www.youtube.com/watch?v=9ATC_uBF8ow
        predef = {
            {0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 5, 0, 3, 0, 8, 0, 2, 0},
            {2, 0, 5, 0, 3, 0, 6, 0, 9},
            {0, 9, 0, 4, 0, 6, 0, 1, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0}};

        horizontal_xvs = {
            {O, O, O, O, O, O, O, O},
            {O, O, O, O, O, O, O, O},
            {O, O, O, O, O, O, O, O},
            {O, O, O, O, O, O, O, O},
            {O, O, O, O, O, O, O, O},
            {O, O, O, O, O, O, O, O},
            {O, O, O, O, O, O, O, O},
            {O, O, O, O, O, O, O, O},
            {O, O, O, O, O, O, O, O}};

        vertical_xvs = {
            {O, O, O, O, O, O, O, O},
            {O, X, O, O, O, O, O, O},
            {X, O, X, O, O, O, O, O},
            {O, X, O, O, O, O, O, O},
            {X, O, X, O, O, O, O, O},
            {O, X, O, O, O, O, O, O},
            {X, O, X, O, O, O, O, O},
            {O, X, O, O, O, O, O, O},
            {O, O, O, O, O, O, O, O}};
    }
    else {
        // https://abcnews.go.com/blogs/headlines/2012/06/can-you-solve-the-hardest-ever-sudoku
        predef = {
            {8, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 3, 6, 0, 0, 0, 0, 0},
            {0, 7, 0, 0, 9, 0, 2, 0, 0},
            {0, 5, 0, 0, 0, 7, 0, 0, 0},
            {0, 0, 0, 0, 4, 5, 7, 0, 0},
            {0, 0, 0, 1, 0, 0, 0, 3, 0},
            {0, 0, 1, 0, 0, 0, 0, 6, 8},
            {0, 0, 8, 5, 0, 0, 0, 1, 0},
            {0, 9, 0, 0, 0, 0, 4, 0, 0}};
    }

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
        for (int c = 0; c < size; ++c) {
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

    if (! vertical_xvs.empty()) {
        for (int c = 0; c < n; ++c)
            for (int r = 0; r < n - 1; ++r)
                switch (vertical_xvs[c][r]) {
                case N:
                    break;
                case V:
                    p.post(LinearEquality{Linear{{1_i, grid[r][c]}, {1_i, grid[r + 1][c]}}, 5_i, true});
                    break;
                case X:
                    p.post(LinearEquality{Linear{{1_i, grid[r][c]}, {1_i, grid[r + 1][c]}}, 10_i, true});
                    break;
                case O:
                    auto sum = p.create_integer_variable(0_i, Integer{n * 2});
                    p.post(NotEquals{sum, 5_c});
                    p.post(NotEquals{sum, 10_c});
                    p.post(LinearEquality{Linear{{1_i, grid[r][c]}, {1_i, grid[r + 1][c]}, {-1_i, sum}}, 0_i, true});
                    break;
                }

        for (int r = 0; r < n; ++r)
            for (int c = 0; c < n - 1; ++c)
                switch (horizontal_xvs[r][c]) {
                case N:
                    break;
                case V:
                    p.post(LinearEquality{Linear{{1_i, grid[r][c]}, {1_i, grid[r][c + 1]}}, 5_i, true});
                    break;
                case X:
                    p.post(LinearEquality{Linear{{1_i, grid[r][c]}, {1_i, grid[r][c + 1]}}, 10_i, true});
                    break;
                case O:
                    auto sum = p.create_integer_variable(0_i, Integer{n * 2});
                    p.post(NotEquals{sum, 5_c});
                    p.post(NotEquals{sum, 10_c});
                    p.post(LinearEquality{Linear{{1_i, grid[r][c]}, {1_i, grid[r][c + 1]}, {-1_i, sum}}, 0_i, true});
                    break;
                }
    }

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
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
            },
            .trace = [&](const CurrentState & s) -> bool {
                for (const auto & row : grid) {
                    bool first = true;
                    for (const auto & box : row) {
                        if (! first)
                            cout << " ";
                        if (s.has_single_value(box))
                            cout << s(box);
                        else
                            cout << ".";

                        first = false;
                    }
                    cout << endl;
                }
                cout << endl;
                return true;
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>("sudoku.opb", "sudoku.veripb") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
