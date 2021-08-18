/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/min_max.hh>
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

    if (1 == argc) {
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
        cerr << "Usage: " << argv[0] << " [ 9 ]" << endl;
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

    visible_north.resize(size);
    for (int c = 0 ; c < size ; ++c) {
        if (north[c] != 0) {
            Linear coeff_vars;
            for (int r = 0 ; r < size ; ++r) {
                coeff_vars.emplace_back(1_i, *visible_north[r][c]);
                // visible_north[r][c] <-> (grid[r][c] > max(grid[r][0..c - 1]))
                if (0 == r)
                    p.post(Equals{ *visible_north[r][c], 1_c });
                else {
                    IntegerVariableID max_predecessors = p.create_integer_variable(1_i, Integer(size));
                    vector<IntegerVariableID> predecessors;
                    for (int rr = 0 ; rr < r ; ++rr)
                        predecessors.push_back(grid[rr][c]);
                    p.post(ArrayMax{ predecessors, max_predecessors });
                    p.post(GreaterThanIff{ grid[r][c], max_predecessors, *visible_north[r][c] == 1_i });
                }
            }
            p.post(LinearEquality{ move(coeff_vars), Integer(north[c]) });
        }
    }

    visible_south.resize(size);
    for (int c = 0 ; c < size ; ++c) {
        if (south[c] != 0) {
            Linear coeff_vars;
            for (int r = 0 ; r < size ; ++r) {
                coeff_vars.emplace_back(1_i, *visible_south[r][c]);
                // visible_south[r][c] <-> (grid[r][c] > max(grid[r][0..c - 1]))
                if (size - 1 == r)
                    p.post(Equals{ *visible_south[r][c], 1_c });
                else {
                    IntegerVariableID max_predecessors = p.create_integer_variable(1_i, Integer(size));
                    vector<IntegerVariableID> predecessors;
                    for (int rr = size - 1 ; rr > r ; --rr)
                        predecessors.push_back(grid[rr][c]);
                    p.post(ArrayMax{ predecessors, max_predecessors });
                    p.post(GreaterThanIff{ grid[r][c], max_predecessors, *visible_south[r][c] == 1_i });
                }
            }
            p.post(LinearEquality{ move(coeff_vars), Integer(south[c]) });
        }
    }

    visible_west.resize(size);
    for (int r = 0 ; r < size ; ++r) {
        if (west[r] != 0) {
            Linear coeff_vars;
            for (int c = 0 ; c < size ; ++c) {
                coeff_vars.emplace_back(1_i, *visible_west[r][c]);
                // visible_west[r][c] <-> (grid[r][c] > max(grid[r][0..c - 1]))
                if (0 == c)
                    p.post(Equals{ *visible_west[r][c], 1_c });
                else {
                    IntegerVariableID max_predecessors = p.create_integer_variable(1_i, Integer(size));
                    vector<IntegerVariableID> predecessors;
                    for (int cc = 0 ; cc < c ; ++cc)
                        predecessors.push_back(grid[r][cc]);
                    p.post(ArrayMax{ predecessors, max_predecessors });
                    p.post(GreaterThanIff{ grid[r][c], max_predecessors, *visible_west[r][c] == 1_i });
                }
            }
            p.post(LinearEquality{ move(coeff_vars), Integer(west[r]) });
        }
    }

    visible_east.resize(size);
    for (int r = 0 ; r < size ; ++r) {
        if (east[r] != 0) {
            Linear coeff_vars;
            for (int c = 0 ; c < size ; ++c) {
                coeff_vars.emplace_back(1_i, *visible_east[r][c]);
                // visible_east[r][c] <-> (grid[r][c] > max(grid[r][0..c - 1]))
                if (size - 1 == c)
                    p.post(Equals{ *visible_east[r][c], 1_c });
                else {
                    IntegerVariableID max_predecessors = p.create_integer_variable(1_i, Integer(size));
                    vector<IntegerVariableID> predecessors;
                    for (int cc = size - 1 ; cc > c ; --cc)
                        predecessors.push_back(grid[r][cc]);
                    p.post(ArrayMax{ predecessors, max_predecessors });
                    p.post(GreaterThanIff{ grid[r][c], max_predecessors, *visible_east[r][c] == 1_i });
                }
            }
            p.post(LinearEquality{ move(coeff_vars), Integer(east[r]) });
        }
    }

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

