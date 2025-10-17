#include <gcs/constraints/min_max.hh>
#include <gcs/constraints/not_equals.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>

#include <cxxopts.hpp>

#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>

using namespace gcs;

using std::cerr;
using std::cout;
using std::cref;
using std::getline;
using std::ifstream;
using std::make_optional;
using std::nullopt;
using std::pair;
using std::string;
using std::vector;

using std::ranges::views::transform;

using fmt::print;
using fmt::println;


auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Program options");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program options")
            ("help", "Display help information")
            ("prove", "Create a proof");

        options.add_options()
            ("file", "DIMACS format file to use for input", cxxopts::value<string>());

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options] [file]", argv[0]);
        println("");
        std::cout << options.help() << std::endl;
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
                    println(cerr, "Error reading p line in input");
                    return EXIT_FAILURE;
                }
                edges.reserve(n_edges);
            }
            else if ("e" == command) {
                int f = 0, t = 0;
                if (! (inf >> f >> t)) {
                    println(cerr, "Error reading e line in input");
                    return EXIT_FAILURE;
                }
                edges.emplace_back(f - 1, t - 1);
            }
            else {
                println(cerr, "Unknown command {} in input", command);
                return EXIT_FAILURE;
            }
        }

        if (0 == size) {
            println(cerr, "Didn't find size in input");
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
                println("{} colours: {}", s(colours) + 1_i, vertices | transform(cref(s)));
                return true;
            },
            .branch = branch_with(variable_order::dom_then_deg(vertices), value_order::smallest_first())},
        options_vars.contains("prove") ? make_optional<ProofOptions>("colour") : nullopt);

    print("{}", stats);

    return EXIT_SUCCESS;
}
