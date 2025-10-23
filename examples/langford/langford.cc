#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/element.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
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
using std::make_optional;
using std::nullopt;
using std::vector;

using fmt::print;
using fmt::println;


auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Knapsack");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()
                ("help", "Display help information")
                ("prove", "Create a proof");

        options.add_options()
            ("size", "Size of the problem to solve", cxxopts::value<int>()->default_value("7"))
            ("all", "Find all solutions");

        options.parse_positional({"size", "all"});
        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options] [size]", argv[0]);
        println("");
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    int k = options_vars["size"].as<int>();

    Problem p;
    vector<IntegerVariableID> position, solution;
    for (int i = 0; i < 2 * k; ++i) {
        position.emplace_back(p.create_integer_variable(0_i, Integer{2 * k - 1}));
        solution.emplace_back(p.create_integer_variable(1_i, Integer{k}));
    }

    p.post(AllDifferent{position});

    for (int i = 0; i < k; ++i) {
        auto i_var = p.create_integer_variable(Integer{i + 1}, Integer{i + 1});
        p.post(Element{i_var, position[i], &solution});
        p.post(Element{i_var, position[i + k], &solution});

        // position[i + k] = position[i] + i + 2
        p.post(PlusGAC{position[i + k], constant_variable(Integer{i + 2}), position[i]});
    }

    auto stats = solve(
        p, [&](const CurrentState & s) -> bool {
            println("solution: {}", solution | std::ranges::views::transform(cref(s)));
            println("position: {}", position | std::ranges::views::transform(cref(s)));
            println("");

            return true;
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>("langford") : nullopt);

    print("{}", stats);

    return EXIT_SUCCESS;
}
