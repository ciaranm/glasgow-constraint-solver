/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/constraints/table.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <chrono>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;

using std::cerr;
using std::cmp_equal;
using std::cout;
using std::endl;
using std::function;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::to_string;
using std::vector;
using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;

using namespace std::literals::string_literals;

auto main(int argc, char * argv[]) -> int
{
    Problem p{Proof{"skyscrapers.opb", "skyscrapers.veripb"}};

    int size;
    vector<vector<int>> predefs;
    vector<int> north, south, east, west;
    bool use_table = false;
    const string usage = " [ instance 5 | 6 | 7 | 9 ] [ table false|true ]";

    if (argc > 3) {
        cerr << "Usage: " << argv[0] << usage << endl;
        return EXIT_FAILURE;
    }

    int instance = 5;
    if (argc >= 2) {
        if (argv[1] == "5"s)
            instance = 5;
        else if (argv[1] == "6"s)
            instance = 6;
        else if (argv[1] == "7"s)
            instance = 7;
        else if (argv[1] == "9"s)
            instance = 9;
        else {
            cerr << "Usage: " << argv[0] << usage << endl;
            return EXIT_FAILURE;
        }
    }

    if (argc >= 3) {
        if (argv[2] == "true"s)
            use_table = true;
        else if (argv[2] == "false"s)
            use_table = false;
        else {
            cerr << "Usage: " << argv[0] << usage << endl;
            return EXIT_FAILURE;
        }
    }

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
        cerr << "Usage: " << argv[0] << usage << endl;
        return EXIT_FAILURE;
    }

    vector<vector<IntegerVariableID>> grid;
    vector<vector<optional<IntegerVariableID>>> visible_north, visible_south, visible_east, visible_west;
    vector<IntegerVariableID> branch_vars;
    for (int r = 0; r < size; ++r) {
        grid.emplace_back();
        if (! use_table) {
            visible_north.emplace_back();
            visible_south.emplace_back();
            visible_east.emplace_back();
            visible_west.emplace_back();
        }
        for (int c = 0; c < size; ++c) {
            grid[r].push_back(p.create_integer_variable(1_i, Integer{size}, "grid" + to_string(r) + "_" + to_string(c)));
            branch_vars.push_back(grid[r][c]);
            if (! use_table) {
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
    }

    p.branch_on(branch_vars);

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

    if (use_table) {
        vector<vector<Integer>> feasible;
        function<auto(vector<Integer> &)->void> build_feasible = [&](vector<Integer> & head) -> void {
            if (cmp_equal(head.size(), size)) {
                int left_visible_count = 0, right_visible_count = 0;

                Integer biggest_from_left = 0_i, biggest_from_right = 0_i;
                for (int c = 0; c < size; ++c) {
                    if (head[c] > biggest_from_left) {
                        ++left_visible_count;
                        biggest_from_left = head[c];
                    }
                }

                for (int c = size - 1; c >= 0; --c) {
                    if (head[c] > biggest_from_right) {
                        ++right_visible_count;
                        biggest_from_right = head[c];
                    }
                }

                head.push_back(0_i);
                head.push_back(Integer(right_visible_count));
                feasible.push_back(head);
                head.at(head.size() - 2) = Integer(left_visible_count);
                feasible.push_back(head);
                head.back() = 0_i;
                feasible.push_back(head);
                head.pop_back();
                head.pop_back();
            }
            else {
                for (Integer i = 1_i; i <= Integer(size); ++i) {
                    bool alldiff = true;
                    for (auto & h : head)
                        if (h == i)
                            alldiff = false;

                    if (alldiff) {
                        head.push_back(i);
                        build_feasible(head);
                        head.pop_back();
                    }
                }
            }
        };

        auto start_time = steady_clock::now();
        vector<Integer> head;
        build_feasible(head);
        cout << "build table time: " << (duration_cast<microseconds>(steady_clock::now() - start_time).count() / 1'000'000.0) << "s" << endl;

        for (int r = 0; r < size; ++r) {
            if (west[r] != 0 || east[r] != 0) {
                vector<IntegerVariableID> row;
                for (int c = 0; c < size; ++c)
                    row.push_back(grid[r][c]);
                row.push_back(constant_variable(Integer(west[r])));
                row.push_back(constant_variable(Integer(east[r])));
                auto tuples_copy = feasible;
                p.post(Table{row, move(tuples_copy)});
            }
        }

        for (int c = 0; c < size; ++c) {
            if (north[c] != 0 || south[c] != 0) {
                vector<IntegerVariableID> col;
                for (int r = 0; r < size; ++r)
                    col.push_back(grid[r][c]);
                col.push_back(constant_variable(Integer(north[c])));
                col.push_back(constant_variable(Integer(south[c])));
                auto tuples_copy = feasible;
                p.post(Table{col, move(tuples_copy)});
            }
        }
    }
    else {
        build_visible_constraints(visible_north, north, true, true);
        build_visible_constraints(visible_south, south, true, false);
        build_visible_constraints(visible_west, west, false, true);
        build_visible_constraints(visible_east, east, false, false);
    }

    auto stats = solve(p, [&](const State & s) -> bool {
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
    });

    cout << stats;

    return EXIT_SUCCESS;
}
