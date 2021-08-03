/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/arithmetic.hh>
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

auto main(int, char * []) -> int
{
    Problem p;

    int size = 5;
    vector<vector<IntegerVariableID> > g1, g2;
    vector<IntegerVariableID> g12;
    for (int x = 0 ; x < size ; ++x) {
        g1.emplace_back();
        g2.emplace_back();
        for (int y = 0 ; y < size ; ++y) {
            g1[x].push_back(p.create_integer_variable(0_i, Integer{ size - 1 }));
            g2[x].push_back(p.create_integer_variable(0_i, Integer{ size - 1 }));
            g12.push_back(p.create_integer_variable(0_i, Integer{ size * size - 1 }));
        }
    }

    for (int x = 0 ; x < size ; ++x)
        for (int y = 0 ; y < size ; ++y) {
            p.post(Div{ g12[x * size + y], constant_variable(Integer{ size }), g1[x][y] });
            p.post(Mod{ g12[x * size + y], constant_variable(Integer{ size }), g2[x][y] });
        }

    for (int x = 0 ; x < size ; ++x) {
        vector<IntegerVariableID> box1, box2;
        for (int y = 0 ; y < size ; ++y) {
            box1.emplace_back(g1[x][y]);
            box2.emplace_back(g2[x][y]);
        }
        p.post(AllDifferent{ box1 });
        p.post(AllDifferent{ box2 });
    }

    for (int y = 0 ; y < size ; ++y) {
        vector<IntegerVariableID> box1, box2;
        for (int x = 0 ; x < size ; ++x) {
            box1.emplace_back(g1[x][y]);
            box2.emplace_back(g2[x][y]);
        }
        p.post(AllDifferent{ box1 });
        p.post(AllDifferent{ box2 });
    }

    p.post(AllDifferent{ g12 });

    // Normal form: first row of each square and first column of first square is 0 1 2 3 ...
    for (int x = 0 ; x < size ; ++x) {
        p.post(Equals{ g1[0][x], constant_variable(Integer{ x }) });
        p.post(Equals{ g2[0][x], constant_variable(Integer{ x }) });
        p.post(Equals{ g1[x][0], constant_variable(Integer{ x }) });
    }

    auto stats = solve(p, [&] (const State & s) -> bool {
            for (int x = 0 ; x < size ; ++x) {
                for (int y = 0 ; y < size ; ++y)
                    cout << s(g1[x][y]) << "," << s(g2[x][y]) << " ";
                cout << endl;
            }
            cout << endl;

            return true;
            });

    cout << stats;

    return EXIT_SUCCESS;
}

