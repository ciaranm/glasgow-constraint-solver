#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include <cxxopts.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;

using std::cerr;
using std::cout;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace std::literals::string_literals;

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Program options");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()                                                //
            ("help", "Display help information")                             //
            ("prove", "Create a proof")                                      //
            ("proof-files-basename", "Basename for the .opb and .pbp files", //
                cxxopts::value<string>()->default_value("cake"))             //
            ("stats", "Print solve statistics")                              //
            ("full-proof-encoding", "Use the longer proof encoding")         //
            ;

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options]", argv[0]);
        println("");
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    Problem p;

    // https://www.minizinc.org/doc-2.5.5/en/modelling.html#an-arithmetic-optimisation-example
    auto banana = p.create_integer_variable(0_i, 100_i, "banana");
    auto chocolate = p.create_integer_variable(0_i, 100_i, "chocolate");
    p.post(WeightedSum{} + 250_i * banana + 200_i * chocolate <= 4000_i);
    p.post(WeightedSum{} + 2_i * banana <= 6_i);
    p.post(WeightedSum{} + 75_i * banana + 150_i * chocolate <= 2000_i);
    p.post(WeightedSum{} + 100_i * banana + 150_i * chocolate <= 500_i);
    p.post(WeightedSum{} + 75_i * chocolate <= 500_i);

    auto profit = p.create_integer_variable(0_i, 107500_i, "profit");
    p.post(WeightedSum{} + 400_i * banana + 450_i * chocolate == 1_i * profit);

    p.maximise(profit);
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                println("banana cakes = {}, chocolate cakes = {}, profit = {}", s(banana), s(chocolate), s(profit));
                return true;
            },
            .branch = branch_with(
                variable_order::dom_then_deg(vector<IntegerVariableID>{banana, chocolate}),
                value_order::largest_first())},
        options_vars.contains("prove")
            ? make_optional<ProofOptions>(ProofFileNames{options_vars["proof-files-basename"].as<string>()},
                  true, options_vars.count("full-proof-encoding"))
            : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
