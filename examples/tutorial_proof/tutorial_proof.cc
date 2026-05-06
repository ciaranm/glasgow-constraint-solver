#include <gcs/constraints/all_different.hh>
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

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Tutorial Proof Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()                                                //
            ("help", "Display help information")                             //
            ("prove", "Create a proof")                                      //
            ("proof-files-basename", "Basename for the .opb and .pbp files", //
                cxxopts::value<string>()->default_value("tutorial_proof"))   //
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
        options_vars.contains("prove")
            ? make_optional<ProofOptions>(ProofFileNames{options_vars["proof-files-basename"].as<string>()},
                  true, options_vars.count("full-proof-encoding"))
            : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
