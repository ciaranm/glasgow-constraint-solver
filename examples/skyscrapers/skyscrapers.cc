/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <vector>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::to_string;
using std::pair;
using std::string;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    Problem p{ Proof{ "skyscrapers.opb", "skyscrapers.veripb" } };

    int size;
    vector<vector<int> > predefs;
    vector<int> north, south, east, west;

    if (1 == argc || (2 == argc && string(argv[1]) == string("5"))) {
        size = 5;
        predefs = {
            { 0, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0 },
            { 0, 0, 5, 0, 0 },
            { 0, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0 }
        };

        north = { 1, 0, 0, 3, 3 };
        south = { 0, 0, 0, 0, 1 };
        east  = { 4, 0, 2, 0, 0 };
        west  = { 0, 0, 3, 0, 4 };
    }
    else if (2 == argc && string(argv[1]) == string("6")) {
        size = 6;
        predefs = {
            { 0, 0, 4, 0, 0, 0 },
            { 0, 0, 2, 0, 0, 0 },
            { 0, 0, 0, 0, 2, 0 },
            { 0, 0, 0, 3, 0, 0 },
            { 0, 0, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0, 1 }
        };

        north = { 1, 2, 2, 2, 3, 4 };
        south = { 4, 1, 2, 3, 2, 2 };
        east  = { 5, 3, 3, 2, 1, 4 };
        west  = { 1, 3, 2, 3, 3, 2 };
    }
    else if (2 == argc && string(argv[1]) == string("7")) {
        size = 7;
        predefs = {
            { 0, 0, 0, 0, 0, 0, 0 },
            { 0, 0, 3, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0, 0, 0 },
            { 4, 0, 0, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0, 0, 0 }
        };

        north = { 0, 0, 5, 1, 3, 4, 0 };
        south = { 0, 4, 0, 4, 4, 0, 3 };
        east  = { 4, 2, 0, 1, 0, 4, 0 };
        west  = { 2, 0, 4, 0, 4, 0, 0 };
    }
    else if (2 == argc && string(argv[1]) == string("9")) {
        size = 9;
        predefs = {
            { 0, 0, 0, 0, 0, 2, 0, 0, 0 },
            { 7, 0, 0, 0, 0, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0, 0, 6, 2, 0 },
            { 0, 0, 0, 0, 3, 0, 0, 0, 0 },
            { 0, 0, 0, 0, 0, 0, 0, 0, 0 },
            { 0, 0, 3, 0, 0, 0, 0, 0, 0 },
            { 0, 3, 0, 5, 0, 0, 0, 0, 0 }
        };

        north = { 0, 0, 0, 6, 0, 6, 2, 2, 5 };
        south = { 0, 0, 5, 3, 3, 3, 0, 4, 0 };
        east  = { 0, 3, 0, 7, 2, 5, 2, 4, 0 };
        west  = { 0, 0, 0, 1, 0, 4, 4, 0, 5 };
    }
    else {
        cerr << "Usage: " << argv[0] << " [ 5 | 6 | 7 | 9 ]" << endl;
        return EXIT_FAILURE;
    }

    vector<vector<IntegerVariableID> > grid;
    vector<vector<optional<IntegerVariableID> > > visible_north, visible_south, visible_east, visible_west;
    vector<IntegerVariableID> branch_vars;
    for (int r = 0 ; r < size ; ++r) {
        grid.emplace_back();
        visible_north.emplace_back();
        visible_south.emplace_back();
        visible_east.emplace_back();
        visible_west.emplace_back();
        for (int c = 0 ; c < size ; ++c) {
            grid[r].push_back(p.create_integer_variable(1_i, Integer{ size }, "grid" + to_string(r) + "_" + to_string(c)));
            branch_vars.push_back(grid[r][c]);
            visible_north[r].push_back(north[c] != 0 ? make_optional(p.create_integer_variable(0_i, 1_i, "visible_north" + to_string(c))) : nullopt);
            visible_south[r].push_back(south[c] != 0 ? make_optional(p.create_integer_variable(0_i, 1_i, "visible_south" + to_string(c))) : nullopt);
            visible_east[r].push_back(east[r] != 0 ? make_optional(p.create_integer_variable(0_i, 1_i, "visible_east" + to_string(c))) : nullopt);
            visible_west[r].push_back(west[r] != 0 ? make_optional(p.create_integer_variable(0_i, 1_i, "visible_west" + to_string(c))) : nullopt);
        }
    }

    p.branch_on(branch_vars);

    for (int r = 0 ; r < size ; ++r)
        p.post(AllDifferent{ grid[r] });

    for (int c = 0 ; c < size ; ++c) {
        vector<IntegerVariableID> column;
        for (int r = 0 ; r < size ; ++r)
            column.push_back(grid[r][c]);
        p.post(AllDifferent{ column });
    }

    for (int r = 0 ; r < size ; ++r)
        for (int c = 0 ; c < size ; ++c)
            if (predefs[r][c] != 0)
                p.post(Equals{ grid[r][c], constant_variable(Integer{ predefs[r][c] }) });

    auto build_visible_constraints = [&] (auto & visible_vars, const auto & target, bool downwards, bool forwards) {
        visible_vars.resize(size);
        for (int c = 0 ; c < size ; ++c) {
            if (target[c] != 0) {
                Linear how_many_visible;
                for (int r = 0 ; r < size ; ++r) {
                    how_many_visible.emplace_back(1_i, *visible_vars[downwards ? r : c][downwards ? c : r]);
                    if (r == (forwards ? 0 : size - 1))
                        p.post(Equals{ *visible_vars[downwards ? r : c][downwards ? c : r], 1_c });
                    else {
                        Linear hiding;
                        for (int rr = (forwards ? 0 : size - 1) ; forwards ? rr < r : rr > r ; forwards ? ++rr : --rr) {
                            hiding.emplace_back(1_i, p.create_integer_variable(0_i, 1_i));
                            p.post(GreaterThanIff{ grid[downwards ? r : c][downwards ? c : r], grid[downwards ? rr : c][downwards ? c : rr], hiding.back().second == 0_i });
                        }
                        auto how_many_hidden = p.create_integer_variable(0_i, Integer(hiding.size()));
                        hiding.emplace_back(-1_i, how_many_hidden);
                        p.post(LinearEquality{ move(hiding), 0_i });
                        p.post(EqualsIff{ how_many_hidden, constant_variable(0_i), *visible_vars[downwards ? r : c][downwards ? c : r] == 1_i });
                    }
                }
                p.post(LinearEquality{ move(how_many_visible), Integer(target[c]) });
            }
        }
    };

    build_visible_constraints(visible_north, north, true, true);
    build_visible_constraints(visible_south, south, true, false);
    build_visible_constraints(visible_west, west, false, true);
    build_visible_constraints(visible_east, east, false, false);

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << "   ";
            for (int c = 0 ; c < size ; ++c)
                cout << " " << (north[c] != 0 ? to_string(north[c]) : " ");
            cout << endl;

            for (int r = 0 ; r < size ; ++r) {
                cout << (west[r] != 0 ? to_string(west[r]) : " ") << "  ";
                for (int c = 0 ; c < size ; ++c)
                    cout << " " << s(grid[r][c]);
                cout << "  " << (east[r] != 0 ? to_string(east[r]) : "");
                cout << endl;
            }

            cout << "   ";
            for (int c = 0 ; c < size ; ++c)
                cout << " " << (south[c] != 0 ? to_string(south[c]) : " ");
            cout << endl;

            cout << endl;
            return true;
            }
    );

    cout << stats;

    return EXIT_SUCCESS;
}

