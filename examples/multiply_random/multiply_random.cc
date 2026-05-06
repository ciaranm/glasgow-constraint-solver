#include <cxxopts.hpp>
#include <gcs/constraints/mult_bc.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <random>
#include <string>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using std::cerr;
using std::cout;
using std::endl;
using std::string;

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Random Multiplication Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                         //
            ("help", "Display help information")                                       //
            ("prove", "Create a proof")                                                //
            ("seed", "Seed for random multiplication constraint (-1 for random seed)", //
                cxxopts::value<int>()->default_value("-1"))                            //
            ("n", "Max bounds from -n..n", cxxopts::value<int>()->default_value("5"))  //
            ("stats", "Print stats")                                                   //
            ("display-problem", "Display problem and solution (if any)")               //
            ("proof-files-basename", "Path and name of the opb and pbp files",                 //
                cxxopts::value<string>()->default_value("multiply_random"));           //

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << options.help() << endl;
        return EXIT_SUCCESS;
    }

    auto n = options_vars["n"].as<int>();
    auto seed = options_vars["seed"].as<int>();
    auto proof_prefix = options_vars["proof-files-basename"].as<string>();
    auto prove = options_vars.contains("prove");
    auto print_stats = options_vars.contains("stats");
    auto display_problem = options_vars.contains("display-problem");

    if (seed == -1) {
        std::random_device rand_dev;
        seed = rand_dev();
    }

    std::mt19937 rng(seed);
    std::uniform_int_distribution<int> lower_dist{-n, n}, add_dist{0, n};

    Problem p{};
    auto x_lower = Integer{lower_dist(rng)};
    auto x_upper = x_lower + Integer{add_dist(rng)};
    auto x = p.create_integer_variable(x_lower, x_upper, "X");
    auto y_lower = Integer{lower_dist(rng)};
    auto y_upper = y_lower + Integer{add_dist(rng)};
    auto y = p.create_integer_variable(y_lower, y_upper, "y");
    auto z_lower = Integer{lower_dist(rng)};
    auto z_upper = z_lower + Integer{add_dist(rng)};
    auto z = p.create_integer_variable(z_lower, z_upper, "z");

    p.post(MultBC{x, y, z});

    if (display_problem) {
        println(cout, "x in {}..{}", x_lower, x_upper);
        println(cout, "y in {}..{}", y_lower, y_upper);
        println(cout, "z in {}..{}", z_lower, z_upper);
    }
    auto stats = solve(
        p, [&](const CurrentState & s) -> bool { 
           if (display_problem) {
            println(cout, "solution: x = {}, y = {}, z = {}", s(x), s(y), s(z));
           }
            return false; },
        prove ? std::make_optional(ProofOptions{proof_prefix}) : std::nullopt);

    if (print_stats) {
        cout << "seed: " << seed << endl;
        cout << stats << endl;
    }
    return EXIT_SUCCESS;
}
