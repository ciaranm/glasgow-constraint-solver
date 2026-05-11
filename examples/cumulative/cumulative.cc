#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <vector>

#include <cxxopts.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using namespace gcs;

using std::cerr;
using std::cref;
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
    cxxopts::Options options("Cumulative Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program options")                                                       //
            ("help", "Display help information")                                                     //
            ("prove", "Create a proof")                                                              //
            ("proof-files-basename", "Basename for the .opb and .pbp files",                         //
                cxxopts::value<string>()->default_value("cumulative"))                               //
            ("stats", "Print solve statistics")                                                      //
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
        println("Five tasks share a single resource of capacity 3.");
        println("Minimise the makespan: the time at which the last task finishes.");
        println("");
        print("{}", options.help());
        return EXIT_SUCCESS;
    }

    // Five tasks on a resource of capacity 3. Lengths and heights are fixed;
    // each task's start time is the decision variable. The schedule must keep
    // the cumulated demand at every time point at or below the capacity.
    vector<Integer> lengths = {3_i, 2_i, 2_i, 1_i, 4_i};
    vector<Integer> heights = {2_i, 1_i, 2_i, 3_i, 1_i};
    Integer capacity = 3_i;
    Integer horizon = 10_i;

    Problem p;
    auto starts = p.create_integer_variable_vector(lengths.size(), 0_i, horizon, "s");

    p.post(Cumulative{starts, lengths, heights, capacity});

    auto makespan = p.create_integer_variable(0_i, horizon + Integer{static_cast<long long>(lengths.size())}, "makespan");
    for (auto i = 0u; i < lengths.size(); ++i)
        p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * makespan + -1_i * starts[i], lengths[i]});

    p.minimise(makespan);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                println("schedule: starts {} makespan {}",
                    starts | std::ranges::views::transform(cref(s)), s(makespan));
                return true;
            }},
        options_vars.contains("prove")
            ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>())
            : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
