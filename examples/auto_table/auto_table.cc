#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/presolvers/auto_table.hh>
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
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");         //

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

    auto v = p.create_integer_variable_vector(5, 1_i, 5_i, "v");
    p.post(AllDifferent{vector{v[0], v[1], v[2]}});
    p.post(AllDifferent{vector{v[2], v[3], v[4]}});
    p.post(WeightedSum{} + 1_i * v[0] + 1_i * v[1] + 1_i * v[2] + 1_i * v[3] + 1_i * v[4] == 10_i);

    p.add_presolver(AutoTable{vector{v[0], v[1], v[2]}});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                println("{} {} {} {} {}", s(v[0]), s(v[1]), s(v[2]), s(v[3]), s(v[4]));
                return true;
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>("auto_table.opb", "auto_table.pbp") : nullopt);

    print("{}", stats);

    return EXIT_SUCCESS;
}
