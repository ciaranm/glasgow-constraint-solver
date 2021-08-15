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
using std::to_string;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    int size = 0;
    vector<pair<int, int> > edges;
    if (1 == argc) {
        size = 7;
        // Robert Janczewski, Marek Kubale, Krzysztof Manuszewski, Konrad Piwakowski:
        // The smallest hard-to-color graph for algorithm DSATUR. Discret. Math. 236(1-3): 151-165 (2001)
        edges = { { 0, 1 }, { 0, 2 }, { 0, 3 }, { 1, 2 }, { 1, 4 }, { 3, 5 }, { 3, 6 }, { 4, 5 }, { 4, 6 }, { 5, 6 } };
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

    Problem p{ Proof{ "colour.opb", "colour.veripb" } };

    vector<IntegerVariableID> vertices;
    for (int v = 0 ; v != size ; ++v)
        vertices.push_back(p.create_integer_variable(0_i, Integer{ size - 1 }, "vertex" + to_string(v)));

    for (auto & [ f, t ] : edges)
        p.post(NotEquals{ vertices[f], vertices[t] });

    IntegerVariableID colours = p.create_integer_variable(0_i, Integer{ size - 1 }, "colours");
    p.post(ArrayMax{ vertices, colours });

    p.branch_on(vertices);
    p.minimise(colours);

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << s(colours) + 1_i << " colours:";
            for (auto & v : vertices)
                cout << " " << s(v);
            cout << endl;

            return true;
            });

    cout << stats;

    return EXIT_SUCCESS;
}

