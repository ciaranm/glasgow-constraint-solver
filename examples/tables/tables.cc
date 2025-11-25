#include <gcs/constraints/table.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include <cxxopts.hpp>

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

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Program options");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()                    //
            ("help", "Display help information") //
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

    auto v1 = p.create_integer_variable(1_i, 4_i, "v1");
    auto v2 = p.create_integer_variable(1_i, 4_i, "v2");
    auto v3 = p.create_integer_variable(1_i, 4_i, "v3");
    auto v4 = p.create_integer_variable(1_i, 4_i, "v4");

    p.post(Table{
        {v1, v2, v3},
        SimpleTuples{
            {1_i, 2_i, 3_i},
            {1_i, 3_i, 2_i},
            {2_i, 1_i, 3_i},
            {2_i, 3_i, 1_i},
            {3_i, 1_i, 2_i},
            {3_i, 2_i, 1_i}}});

    p.post(Table{
        {v1, v4},
        WildcardTuples{
            {1_i, Wildcard{}},
            {2_i, 2_i},
            {3_i, 3_i},
            {4_i, 4_i}}});

    p.post(Table{
        {v1, v2, v3, v4},
        WildcardTuples{
            {1_i, 1_i, Wildcard{}, Wildcard{}},
            {Wildcard{}, 1_i, 1_i, Wildcard{}},
            {Wildcard{}, Wildcard{}, 1_i, 1_i},
            {2_i, 2_i, Wildcard{}, Wildcard{}},
            {Wildcard{}, 2_i, 2_i, Wildcard{}},
            {Wildcard{}, Wildcard{}, 2_i, 2_i},
            {3_i, 3_i, Wildcard{}, Wildcard{}},
            {Wildcard{}, 3_i, 3_i, Wildcard{}},
            {Wildcard{}, Wildcard{}, 3_i, 3_i},
            {4_i, 4_i, Wildcard{}, Wildcard{}},
            {Wildcard{}, 4_i, 4_i, Wildcard{}},
            {Wildcard{}, Wildcard{}, 4_i, 4_i},
        }});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                println("{} {} {} {}", s(v1), s(v2), s(v3), s(v4));
                return true;
            },
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>("tables") : nullopt);

    print("{}", stats);

    return EXIT_SUCCESS;
}
