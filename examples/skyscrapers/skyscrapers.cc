/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <chrono>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::string;
using std::to_string;
using std::vector;
using std::chrono::microseconds;

namespace po = boost::program_options;

using namespace std::literals::string_literals;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");

    po::options_description all_options{"All options"};
    all_options.add_options()                                                         //
        ("instance", po::value<int>()->default_value(7), "Problem instance to solve") //
        ("all", "Find all solutions");

    all_options.add(display_options);

    po::positional_options_description positional_options;
    positional_options
        .add("instance", -1);

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
        cout << "Usage: " << argv[0] << " [options] [instance]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    int instance = options_vars["instance"].as<int>();

    Problem p = options_vars.contains("prove") ? Problem{ProofOptions{"skyscrapers.opb", "skyscrapers.veripb"}} : Problem{};

    vector<vector<int>> predefs;
    vector<int> north, south, east, west;

    int size = 0;
    if (instance == 5) {
        size = 5;
        predefs = {
            {0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0},
            {0, 0, 5, 0, 0},
            {0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0}};

        north = {1, 0, 0, 3, 3};
        south = {0, 0, 0, 0, 1};
        east = {4, 0, 2, 0, 0};
        west = {0, 0, 3, 0, 4};
    }
    else if (instance == 6) {
        size = 6;
        predefs = {
            {0, 0, 4, 0, 0, 0},
            {0, 0, 2, 0, 0, 0},
            {0, 0, 0, 0, 2, 0},
            {0, 0, 0, 3, 0, 0},
            {0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 1}};

        north = {1, 2, 2, 2, 3, 4};
        south = {4, 1, 2, 3, 2, 2};
        east = {5, 3, 3, 2, 1, 4};
        west = {1, 3, 2, 3, 3, 2};
    }
    else if (instance == 7) {
        size = 7;
        predefs = {
            {0, 0, 0, 0, 0, 0, 0},
            {0, 0, 3, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0},
            {4, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0}};

        north = {0, 0, 5, 1, 3, 4, 0};
        south = {0, 4, 0, 4, 4, 0, 3};
        east = {4, 2, 0, 1, 0, 4, 0};
        west = {2, 0, 4, 0, 4, 0, 0};
    }
    else if (instance == 9) {
        size = 9;
        predefs = {
            {0, 0, 0, 0, 0, 2, 0, 0, 0},
            {7, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 6, 2, 0},
            {0, 0, 0, 0, 3, 0, 0, 0, 0},
            {0, 0, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 3, 0, 0, 0, 0, 0, 0},
            {0, 3, 0, 5, 0, 0, 0, 0, 0}};

        north = {0, 0, 0, 6, 0, 6, 2, 2, 5};
        south = {0, 0, 5, 3, 3, 3, 0, 4, 0};
        east = {0, 3, 0, 7, 2, 5, 2, 4, 0};
        west = {0, 0, 0, 1, 0, 4, 4, 0, 5};
    }
    else {
        cerr << "Unknown instance (try size 5, 6, 7, or 9)" << endl;
        return EXIT_FAILURE;
    }

    vector<vector<IntegerVariableID>> grid;
    vector<vector<optional<IntegerVariableID>>> visible_north, visible_south, visible_east, visible_west;
    vector<IntegerVariableID> branch_vars;
    for (int r = 0; r < size; ++r) {
        grid.emplace_back();
        visible_north.emplace_back();
        visible_south.emplace_back();
        visible_east.emplace_back();
        visible_west.emplace_back();
        for (int c = 0; c < size; ++c) {
            grid[r].push_back(p.create_integer_variable(1_i, Integer{size}, "grid" + to_string(r) + "_" + to_string(c)));
            branch_vars.push_back(grid[r][c]);
            visible_north[r].push_back(north[c] != 0
                    ? make_optional(p.create_integer_variable(0_i, 1_i, "visible_north" + to_string(c)))
                    : nullopt);
            visible_south[r].push_back(south[c] != 0
                    ? make_optional(p.create_integer_variable(0_i, 1_i, "visible_south" + to_string(c)))
                    : nullopt);
            visible_east[r].push_back(east[r] != 0
                    ? make_optional(p.create_integer_variable(0_i, 1_i, "visible_east" + to_string(c)))
                    : nullopt);
            visible_west[r].push_back(west[r] != 0
                    ? make_optional(p.create_integer_variable(0_i, 1_i, "visible_west" + to_string(c)))
                    : nullopt);
        }
    }

    for (int r = 0; r < size; ++r)
        p.post(AllDifferent{grid[r]});

    for (int c = 0; c < size; ++c) {
        vector<IntegerVariableID> column;
        for (int r = 0; r < size; ++r)
            column.push_back(grid[r][c]);
        p.post(AllDifferent{column});
    }

    for (int r = 0; r < size; ++r)
        for (int c = 0; c < size; ++c)
            if (predefs[r][c] != 0)
                p.post(Equals{grid[r][c], constant_variable(Integer{predefs[r][c]})});

    auto build_visible_constraints = [&](auto & visible_vars, const auto & target, bool downwards, bool forwards) {
        visible_vars.resize(size);
        for (int c = 0; c < size; ++c) {
            if (0 == target[c])
                continue;

            // (Assuming we're doing North) How many things above us are visible?
            Linear how_many_visible;
            for (int r = 0; r < size; ++r) {
                how_many_visible.emplace_back(1_i, *visible_vars[downwards ? r : c][downwards ? c : r]);
                if (r == (forwards ? 0 : size - 1)) {
                    // We're the topmost thing, so we're visible
                    p.post(Equals{*visible_vars[downwards ? r : c][downwards ? c : r], 1_c});
                }
                else {
                    // How many things above us will hide us? We're visible iff it's zero
                    Linear hiding;
                    for (int rr = (forwards ? 0 : size - 1); forwards ? rr < r : rr > r; forwards ? ++rr : --rr) {
                        hiding.emplace_back(1_i, p.create_integer_variable(0_i, 1_i));
                        p.post(GreaterThanIff{
                            grid[downwards ? r : c][downwards ? c : r],
                            grid[downwards ? rr : c][downwards ? c : rr],
                            hiding.back().second == 0_i});
                    }
                    auto how_many_hidden = p.create_integer_variable(0_i, Integer(hiding.size()));
                    hiding.emplace_back(-1_i, how_many_hidden);
                    p.post(LinearEquality{move(hiding), 0_i});
                    p.post(EqualsIff{
                        how_many_hidden,
                        constant_variable(0_i),
                        *visible_vars[downwards ? r : c][downwards ? c : r] == 1_i});
                }
            }
            p.post(LinearEquality{move(how_many_visible), Integer(target[c]), true});
        }
    };

    build_visible_constraints(visible_north, north, true, true);
    build_visible_constraints(visible_south, south, true, false);
    build_visible_constraints(visible_west, west, false, true);
    build_visible_constraints(visible_east, east, false, false);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "   ";
                for (int c = 0; c < size; ++c)
                    cout << " " << (north[c] != 0 ? to_string(north[c]) : " ");
                cout << endl;

                for (int r = 0; r < size; ++r) {
                    cout << (west[r] != 0 ? to_string(west[r]) : " ") << "  ";
                    for (int c = 0; c < size; ++c)
                        cout << " " << s(grid[r][c]);
                    cout << "  " << (east[r] != 0 ? to_string(east[r]) : "");
                    cout << endl;
                }

                cout << "   ";
                for (int c = 0; c < size; ++c)
                    cout << " " << (south[c] != 0 ? to_string(south[c]) : " ");
                cout << endl;

                cout << endl;
                return true;
            },
            .branch = branch_on_dom_then_deg(p, branch_vars)});

    cout << stats;

    return EXIT_SUCCESS;
}
