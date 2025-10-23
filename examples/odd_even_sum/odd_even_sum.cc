#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <string>

#include <cxxopts.hpp>

#include <fmt/core.h>
#include <fmt/ostream.h>

using namespace gcs;

using std::cerr;
using std::cout;
using std::make_optional;
using std::nullopt;
using std::string;

using fmt::print;
using fmt::println;


auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Odd_even_sum Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")
            ("help", "Display help information")
            ("prove", "Create a proof");
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

    auto a = p.create_integer_variable(0_i, 5_i, "a");
    auto b = p.create_integer_variable(0_i, 5_i, "b");
    auto c = p.create_integer_variable(0_i, 5_i, "c");
    auto d = p.create_integer_variable(0_i, 10_i, "d");
    auto e = p.create_integer_variable(0_i, 2_i, "e");

    p.post(LinearEquality{WeightedSum{} + 2_i * a + 2_i * b + 2_i * c + -2_i * d + 1_i * e, 1_i, true});
    p.post(LinearEquality{WeightedSum{} + -2_i * a + 2_i * b + -2_i * c + 2_i * d + 1_i * e, 1_i, true});

    auto stats = solve(
        p, [&](const CurrentState & s) -> bool {
            println("{} {} {} {} {}", s(a), s(b), s(c), s(d), s(e));
            return true;
        },
        options_vars.count("prove") ? make_optional<ProofOptions>("odd_even_sum") : nullopt);

    print("{}", stats);

    return EXIT_SUCCESS;
}
