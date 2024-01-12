#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include <boost/program_options.hpp>

#include <fmt/core.h>
#include <fmt/ostream.h>

using namespace gcs;

using std::cerr;
using std::cout;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

using fmt::print;
using fmt::println;

using namespace std::literals::string_literals;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()                                 //
        ("help", "Display help information")                      //
        ("prove", "Create a proof")                               //
        ("full-proof-encoding", "Use the longer proof encoding"); //

    po::options_description all_options{"All options"};

    all_options.add(display_options);

    po::variables_map options_vars;

    try {
        po::store(po::command_line_parser(argc, argv)
                      .options(all_options)
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
        println("Usage: {} [options]", argv[0]);
        println("");
        display_options.print(cout);
        return EXIT_SUCCESS;
    }

    Problem p;

    // https://www.minizinc.org/doc-2.5.5/en/modelling.html#an-arithmetic-optimisation-example
    auto banana = p.create_integer_variable(0_i, 100_i);
    auto chocolate = p.create_integer_variable(0_i, 100_i);
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
            .branch = branch_on_dom_then_deg(vector<IntegerVariableID>{banana, chocolate}),
            .guess = guess_smallest_value_first() //
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>(
                                             "cake.opb", "cake.veripb", true, options_vars.count("full-proof-encoding"))
                                       : nullopt);

    print("{}", stats);

    return EXIT_SUCCESS;
}
