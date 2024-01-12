#include <gcs/constraints/min_max.hh>
#include <gcs/constraints/not_equals.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <ranges>
#include <vector>

#include <boost/program_options.hpp>

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

#if __cpp_lib_ranges >= 202110L
using std::ranges::views::transform;
#endif

using fmt::print;
using fmt::println;

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
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options] [file]", argv[0]);
        println("");
        display_options.print(cout);
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
#if __cpp_lib_ranges >= 202110L
                println("{} colours: {}", s(colours) + 1_i, vertices | transform(cref(s)));
#else
                println("{} colours: {}", s(colours) + 1_i, s(vertices));
#endif
                return true;
            },
            .branch = branch_on_dom_then_deg(vertices)},
        options_vars.contains("prove") ? make_optional<ProofOptions>("colour.opb", "colour.veripb") : nullopt);

    print("{}", stats);

    return EXIT_SUCCESS;
}
