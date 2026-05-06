#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
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

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Money Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()                                                //
            ("help", "Display help information")                             //
            ("prove", "Create a proof")                                      //
            ("proof-files-basename", "Basename for the .opb and .pbp files", //
                cxxopts::value<string>()->default_value("money"))            //
            ("stats", "Print solve statistics")                              //
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

    auto s = p.create_integer_variable(1_i, 9_i, "s");
    auto e = p.create_integer_variable(0_i, 9_i, "e");
    auto n = p.create_integer_variable(0_i, 9_i, "n");
    auto d = p.create_integer_variable(0_i, 9_i, "d");
    auto m = p.create_integer_variable(1_i, 9_i, "m");
    auto o = p.create_integer_variable(0_i, 9_i, "o");
    auto r = p.create_integer_variable(0_i, 9_i, "r");
    auto y = p.create_integer_variable(0_i, 9_i, "y");

    vector<IntegerVariableID> vars{s, e, n, d, m, o, r, y};
    p.post(AllDifferent{vars});

    // clang-format off
    p.post(WeightedSum{}
            +                 1000_i * s +  100_i * e +  10_i * n +  1_i * d
            +                 1000_i * m +  100_i * o +  10_i * r +  1_i * e
            + -10000_i * m + -1000_i * o + -100_i * n + -10_i * e + -1_i * y == 0_i);
    // clang-format on

    auto stats = solve(
        p, [&](const CurrentState & state) -> bool {
            println(" {}{}{}{}", state(s), state(e), state(n), state(d));
            println(" {}{}{}{}", state(m), state(o), state(r), state(e));
            println("{}{}{}{}{}", state(m), state(o), state(n), state(e), state(y));
            println("");

            return true;
        },
        options_vars.contains("prove")
            ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>())
            : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
