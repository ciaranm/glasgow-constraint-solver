#include <gcs/constraints/abs.hh>
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/constraints/not_equals.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include <boost/program_options.hpp>

#include <fmt/core.h>
#include <fmt/ranges.h>

using namespace gcs;

using std::cerr;
using std::cout;
using std::make_optional;
using std::nullopt;
using std::pair;
using std::string;
using std::to_string;
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
    all_options.add_options()                    //
        ("abs", "Use abs constraint")            //
        ("gac", "Use GAC on the sum constraint") //
        ;

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
        println("Usage: {} [options] [size]", argv[0]);
        println("");
        display_options.print(cout);
        return EXIT_SUCCESS;
    }

    Problem p;

    auto xs = p.create_integer_variable_vector(8, 1_i, 8_i, "box");
    p.post(AllDifferent{xs});

    vector<pair<int, int>> edges{{0, 1}, {0, 2}, {0, 3}, {0, 4},
        {1, 3}, {1, 4}, {1, 5}, {2, 3}, {2, 6}, {3, 4}, {3, 6},
        {3, 7}, {4, 5}, {4, 6}, {4, 7}, {5, 7}, {6, 7}};

    vector<IntegerVariableID> diffs, abs_diffs;
    for (auto & [x1, x2] : edges) {
        diffs.emplace_back(p.create_integer_variable(-7_i, 7_i, "diff" + to_string(x1) + "_" + to_string(x2)));
        if (options_vars.contains("abs")) {
            abs_diffs.emplace_back(p.create_integer_variable(2_i, 7_i, "absdiff" + to_string(x1) + "_" + to_string(x2)));
            p.post(Abs{diffs.back(), abs_diffs.back()});
        }
        else {
            p.post(NotEquals{diffs.back(), 0_c});
            p.post(NotEquals{diffs.back(), 1_c});
            p.post(NotEquals{diffs.back(), -1_c});
        }

        p.post(LinearEquality{WeightedSum{} + 1_i * xs[x1] + -1_i * xs[x2] + -1_i * diffs.back(), 0_i, options_vars.contains("gac")});
    }

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                println("  {} {}", s(xs[0]), s(xs[1]));
                println("{} {} {} {}", s(xs[2]), s(xs[3]), s(xs[4]), s(xs[5]));
                println("  {} {}", s(xs[6]), s(xs[7]));
                println("");
                return true;
            },
            .branch = branch_with(variable_order::dom_then_deg(xs), value_order::smallest_first())},
        options_vars.contains("prove") ? make_optional<ProofOptions>("crystal_maze.opb", "crystal_maze.pbp") : nullopt);

    print("{}", stats);

    return EXIT_SUCCESS;
}
