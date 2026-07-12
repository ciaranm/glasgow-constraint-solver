#include <gcs/constraints/equals.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <optional>
#include <ranges>
#include <vector>

#include <cxxopts.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using namespace gcs;

using std::cerr;
using std::cref;
using std::getline;
using std::ifstream;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::vector;

using std::ranges::views::transform;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

namespace
{
    // Map a dom-wdeg variant string to a weighting scheme, for the --branch flag.
    auto scheme_from_string(const string & name) -> optional<WeightingScheme>
    {
        using enum WeightingScheme;
        if (name == "classic")
            return Classic;
        if (name == "ia")
            return InitialArity;
        if (name == "ca")
            return CurrentArity;
        if (name == "id")
            return InitialDomain;
        if (name == "cd")
            return CurrentDomain;
        if (name == "ca.cd" || name == "cacd")
            return CurrentArityCurrentDomain;
        if (name == "chs")
            return ConflictHistorySearch;
        return nullopt;
    }

    // Build the brancher named by --branch over the given variables: "dom-then-deg",
    // or "dom-wdeg" (the library default scheme) optionally suffixed with a scheme,
    // e.g. "dom-wdeg:classic".
    auto brancher_from_string(const string & spec, const vector<IntegerVariableID> & vars) -> optional<BranchHeuristic>
    {
        if (spec == "dom-then-deg")
            return branch_with(variable_order::dom_then_deg(vars), value_order::smallest_first());
        if (spec == "dom-wdeg")
            return branch_with(variable_order::dom_wdeg(vars), value_order::smallest_first());
        if (spec.starts_with("dom-wdeg:")) {
            auto scheme = scheme_from_string(spec.substr(spec.find(':') + 1));
            if (! scheme)
                return nullopt;
            return branch_with(variable_order::dom_wdeg(vars, *scheme), value_order::smallest_first());
        }
        return nullopt;
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Program options");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program options")                               //
            ("help", "Display help information")                             //
            ("prove", "Create a proof")                                      //
            ("proof-files-basename", "Basename for the .opb and .pbp files", //
                cxxopts::value<string>()->default_value("colour"))           //
            ("stats", "Print solve statistics")                              //
            ("branch",
                "Branching heuristic: dom-then-deg, or dom-wdeg[:VARIANT] "          //
                "(VARIANT one of classic, ia, ca, id, cd, ca.cd, chs)",              //
                cxxopts::value<string>()->default_value("dom-then-deg"))             //
            ("restarts", "Restart on a Luby schedule with the given conflict scale", //
                cxxopts::value<unsigned long long>()->implicit_value("100"))         //
            ("colours",
                "Decision variant: ask whether the graph is K-colourable "              //
                "(rather than minimising the number of colours)",                       //
                cxxopts::value<int>())                                                  //
            ("first", "Stop at the first solution rather than enumerating all of them") //
            ;

        options.add_options()("file", "DIMACS format file to use for input", cxxopts::value<string>());

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

    // In the decision variant we ask whether the graph is K-colourable: each
    // vertex takes a colour in 0..K-1 and there is no objective. Otherwise we
    // minimise the largest colour used.
    auto k_colours = options_vars.contains("colours") ? make_optional(options_vars["colours"].as<int>()) : nullopt;
    auto vertex_max = k_colours ? Integer{*k_colours - 1} : Integer{size - 1};

    auto vertices = p.create_integer_variable_vector(size, 0_i, vertex_max, "vertex");

    for (auto & [f, t] : edges)
        p.post(NotEquals{vertices[f], vertices[t]});

    if (! k_colours) {
        IntegerVariableID colours = p.create_integer_variable(0_i, Integer{size - 1}, "colours");
        p.post(ArrayMax{vertices, colours});
        p.minimise(colours);
    }

    auto brancher = brancher_from_string(options_vars["branch"].as<string>(), vertices);
    if (! brancher) {
        println(cerr, "Error: unknown --branch value {}", options_vars["branch"].as<string>());
        return EXIT_FAILURE;
    }

    auto restarts =
        options_vars.contains("restarts") ? make_optional(RestartSchedule::luby(options_vars["restarts"].as<unsigned long long>())) : nullopt;

    auto stop_at_first = k_colours.has_value() || options_vars.contains("first");

    auto stats = solve_with(p, //
        SolveCallbacks{        //
            .solution = [&](const CurrentState & s) -> bool {
                if (k_colours)
                    println("{}-colouring: {}", *k_colours, vertices | transform(cref(s)));
                else
                    println("{} colours: {}", s(*p.optional_minimise_variable()) + 1_i, vertices | transform(cref(s)));
                return ! stop_at_first;
            },
            .branch = *brancher,
            .restarts = restarts},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
