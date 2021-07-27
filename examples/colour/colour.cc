/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/min_max.hh>
#include <gcs/constraints/comparison.hh>
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
using std::getline;
using std::pair;
using std::string;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    int size = 0;
    vector<pair<int, int> > edges;
    if (1 == argc) {
        size = 12;
        edges = {
        { 0, 1 }, { 0, 4 }, { 0, 7 }, { 0, 9 }, { 0, 10 }, { 0, 11 },
        { 1, 4 }, { 1, 7 }, { 1, 9 },
        { 2, 3 }, { 2, 5 }, { 2, 9 }, { 2, 10 },
        { 3, 5 },
        { 4, 7 },
        { 5, 6 }, { 5, 11 },
        { 6, 8 }, { 6, 10 }, { 6, 11 },
        { 7, 8 },
        { 8, 9 }, { 8, 10 }, { 8, 11 },
        { 9, 10 } };
    }
    else if (2 == argc) {
        ifstream inf{ argv[1] };
        string command;
        while (inf >> command) {
            if ("c" == command)
                getline(inf, command);
            else if ("p" == command) {
                int n_edges;
                if (! (inf >> command >> size >> n_edges)) {
                    cerr << "Error reading p line in input" << endl;
                    return EXIT_FAILURE;
                }
                edges.reserve(n_edges);
            }
            else if ("e" == command) {
                int f, t;
                if (! (inf >> f >> t)) {
                    cerr << "Error reading e line in input" << endl;
                    return EXIT_FAILURE;
                }
                edges.emplace_back(f - 1, t - 1);
            }
            else {
                cerr << "Unknown command " << command << " in input" << endl;
                return EXIT_FAILURE;
            }
        }

        if (0 == size) {
            cerr << "Didn't find size in input" << endl;
            return EXIT_FAILURE;
        }
    }
    else {
        cerr << "Usage: " << argv[0] << " [problemfile]" << endl;
        cerr << "File format is DIMACS" << endl;
        return EXIT_FAILURE;
    }

    Problem p;

    vector<IntegerVariableID> vertices;
    for (int v = 0 ; v != size ; ++v)
        vertices.push_back(p.create_integer_variable(0_i, Integer{ size - 1 }));

    for (auto & [ f, t ] : edges)
        p.post(NotEquals{ vertices[f], vertices[t] });

    p.branch_on(vertices);

    IntegerVariableID colours = p.create_integer_variable(0_i, Integer{ size - 1 });
    p.post(ArrayMax{ vertices, colours });

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << s(colours) + 1_i << " colours:";
            for (auto & v : vertices)
                cout << " " << s(v);
            cout << endl;
            p.post(LessThan{ colours, constant_variable(s(colours)) });

            return true;
            });

    cout << stats;

    return EXIT_SUCCESS;
}

