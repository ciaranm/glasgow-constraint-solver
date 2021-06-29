/* vim: set sw=4 sts=4 et foldmethod=syntax : */

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
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    if (2 != argc) {
        cerr << "Usage: " << argv[0] << " problemfile" << endl;
        cerr << "File format is nine lines of nine values 1-9, or 0 means blank" << endl;
        return EXIT_FAILURE;
    }

    vector<vector<int> > predefs(9, vector<int>(9, 0));
    {
        ifstream inf{ argv[1] };
        for (int x = 0 ; x < 9 ; ++x)
            for (int y = 0 ; y < 9 ; ++y)
                if (! (inf >> predefs[x][y])) {
                    cerr << "Error reading input file" << endl;
                    return EXIT_FAILURE;
                }
    }

    Problem p;

    vector<vector<IntegerVariableID> > grid;
    for (int x = 0 ; x < 9 ; ++x) {
        grid.emplace_back();
        for (int y = 0 ; y < 9 ; ++y)
            grid[x].push_back(p.allocate_integer_variable(1_i, 9_i));
    }

    for (int x = 0 ; x < 9 ; ++x) {
        vector<IntegerVariableID> box;
        for (int y = 0 ; y < 9 ; ++y)
            box.emplace_back(grid[x][y]);
        p.all_different(box);
    }

    for (int y = 0 ; y < 9 ; ++y) {
        vector<IntegerVariableID> box;
        for (int x = 0 ; x < 9 ; ++x)
            box.emplace_back(grid[x][y]);
        p.all_different(box);
    }

    for (int x = 0 ; x < 3 ; ++x) {
        for (int y = 0 ; y < 3 ; ++y) {
            vector<IntegerVariableID> box;
            for (int xx = 0 ; xx < 3 ; ++xx)
                for (int yy = 0 ; yy < 3 ; ++yy)
                    box.emplace_back(grid[3 * x + xx][3 * y + yy]);
            p.all_different(box);
        }
    }

    for (int x = 0 ; x < 9 ; ++x)
        for (int y = 0 ; y < 9 ; ++y)
            if (predefs[x][y] != 0)
                p.cnf({ grid[x][y] == Integer{ predefs[x][y] } });

    auto stats = solve(p, [&] (const State & s) -> bool {
            for (int x = 0 ; x < 9 ; ++x) {
                for (int y = 0 ; y < 9 ; ++y)
                    cout << s(grid[x][y]) << " ";
                cout << endl;
            }
            cout << endl;

            return true;
            });

    cout << "recursions: " << stats.recursions << endl;
    cout << "max depth:  " << stats.max_depth << endl;
    cout << "solve time: " << (stats.solve_time.count() / 1'000'000.0d) << "s" << endl;

    return EXIT_SUCCESS;
}

