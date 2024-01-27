#include <gcs/constraints/all_different.hh>
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

    auto va = p.create_integer_variable(1_i, 5_i, "a");
    auto vb = p.create_integer_variable(1_i, 2_i, "b");
    auto vc = p.create_integer_variable(2_i, 3_i, "c");
    auto vd = p.create_integer_variable(2_i, 3_i, "d");
    p.post(AllDifferent({va, vb, vc, vd}));
    p.post(WeightedSum{} + 1_i * va + 1_i * vb + 1_i * vc <= 9_i);

    auto obj = p.create_integer_variable(0_i, 10000_i, "obj");
    p.post(WeightedSum{} + 2_i * va + 3_i * vd == 1_i * obj);

    p.minimise(obj);
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                println("a = {} b = {} c = {} d = {} obj = {}", s(va), s(vb), s(vc), s(vd), s(obj));
                return true;
            },
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>(
                                             "tutorial_proof.opb", "tutorial_proof.pbp", true, options_vars.count("full-proof-encoding"))
                                       : nullopt);

    print("{}", stats);

    return EXIT_SUCCESS;
}
