#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>

#include <boost/program_options.hpp>

#include <fmt/core.h>
#include <fmt/ostream.h>

using namespace gcs;

using std::cerr;
using std::cout;
using std::ifstream;
using std::make_optional;
using std::nullopt;
using std::vector;

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
    all_options.add_options()                                                         //
        ("size", po::value<int>()->default_value(88), "Size of the problem to solve") //
        ("all", "Find all solutions");

    all_options.add(display_options);

    po::positional_options_description positional_options;
    positional_options
        .add("size", -1);

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
        println("Usage: {} [options] [size]", argv[0]);
        println("");
        display_options.print(cout);
        return EXIT_SUCCESS;
    }

    Problem p;
    int size = options_vars["size"].as<int>();

    vector<vector<IntegerVariableID>> g1, g2;
    vector<IntegerVariableID> g12;
    for (int x = 0; x < size; ++x) {
        g1.emplace_back();
        g2.emplace_back();
        for (int y = 0; y < size; ++y) {
            g1[x].push_back(p.create_integer_variable(0_i, Integer{size - 1}));
            g2[x].push_back(p.create_integer_variable(0_i, Integer{size - 1}));
            g12.push_back(p.create_integer_variable(0_i, Integer{size * size - 1}));
        }
    }

    for (int x = 0; x < size; ++x)
        for (int y = 0; y < size; ++y) {
            p.post(Div{g12[x * size + y], constant_variable(Integer{size}), g1[x][y]});
            p.post(Mod{g12[x * size + y], constant_variable(Integer{size}), g2[x][y]});
        }

    for (int x = 0; x < size; ++x) {
        vector<IntegerVariableID> box1, box2;
        for (int y = 0; y < size; ++y) {
            box1.emplace_back(g1[x][y]);
            box2.emplace_back(g2[x][y]);
        }
        p.post(AllDifferent{box1});
        p.post(AllDifferent{box2});
    }

    for (int y = 0; y < size; ++y) {
        vector<IntegerVariableID> box1, box2;
        for (int x = 0; x < size; ++x) {
            box1.emplace_back(g1[x][y]);
            box2.emplace_back(g2[x][y]);
        }
        p.post(AllDifferent{box1});
        p.post(AllDifferent{box2});
    }

    p.post(AllDifferent{g12});

    // Normal form: first row of each square and first column of first square is 0 1 2 3 ...
    for (int x = 0; x < size; ++x) {
        p.post(Equals{g1[0][x], constant_variable(Integer{x})});
        p.post(Equals{g2[0][x], constant_variable(Integer{x})});
        p.post(Equals{g1[x][0], constant_variable(Integer{x})});
    }

    auto stats = solve(
        p, [&](const CurrentState & s) -> bool {
            for (int x = 0; x < size; ++x) {
                for (int y = 0; y < size; ++y)
                    print("{},{} ", s(g1[x][y]), s(g2[x][y]));
                println("");
            }
            println("");

            return true;
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>("ortho_latin") : nullopt);

    print("{}", stats);

    return EXIT_SUCCESS;
}
