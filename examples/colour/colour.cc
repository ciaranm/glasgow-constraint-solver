/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/equals.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::getline;
using std::ifstream;
using std::make_optional;
using std::nullopt;
using std::pair;
using std::string;
using std::vector;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");

    po::options_description all_options{"All options"};
    all_options.add_options() //
        ("file", po::value<string>(), "DIMACS format file to use for input");

    all_options.add(display_options);

    po::positional_options_description positional_options;
    positional_options
        .add("file", -1);

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
        cout << "Usage: " << argv[0] << " [options] [file]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    vector<pair<int, int>> edges;
    int size;
    if (! options_vars.contains("file")) {
        size = 7;
        // Robert Janczewski, Marek Kubale, Krzysztof Manuszewski, Konrad Piwakowski:
        // The smallest hard-to-color graph for algorithm DSATUR. Discret. Math. 236(1-3): 151-165 (2001)
        edges = {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 4}, {3, 5}, {3, 6}, {4, 5}, {4, 6}, {5, 6}};
    }
    else {
        ifstream inf{options_vars["file"].as<string>()};
        string command;
        while (inf >> command) {
            if ("c" == command)
                getline(inf, command);
            else if ("p" == command) {
                int n_edges = 0;
                if (! (inf >> command >> size >> n_edges)) {
                    cerr << "Error reading p line in input" << endl;
                    return EXIT_FAILURE;
                }
                edges.reserve(n_edges);
            }
            else if ("e" == command) {
                int f = 0, t = 0;
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

    Problem p;

    auto vertices = p.create_integer_variable_vector(size, 0_i, Integer{size - 1}, "vertex");

    for (auto & [f, t] : edges)
        p.post(NotEquals{vertices[f], vertices[t]});

    IntegerVariableID colours = p.create_integer_variable(0_i, Integer{size - 1}, "colours");
    p.post(ArrayMax{vertices, colours});

    p.minimise(colours);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << s(colours) + 1_i << " colours:";
                for (auto & v : vertices)
                    cout << " " << s(v);
                cout << endl;

                return true;
            },
            .branch = branch_on_dom_then_deg(p, vertices)},
        options_vars.contains("prove") ? make_optional<ProofOptions>("colour.opb", "colour.veripb") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
