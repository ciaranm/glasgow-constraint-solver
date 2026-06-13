#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/element.hh>
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
using std::cout;
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

using std::optional;

namespace
{
    // Map a dom-wdeg variant string to a weighting scheme, for the --branch flag.
    auto scheme_from_string(const string & name) -> optional<WeightingScheme>
    {
        using enum WeightingScheme;
        if (name == "classic")
            return Classic;
        if (name == "ia")
            return InitialArity;
        if (name == "ca")
            return CurrentArity;
        if (name == "id")
            return InitialDomain;
        if (name == "cd")
            return CurrentDomain;
        if (name == "ca.cd" || name == "cacd")
            return CurrentArityCurrentDomain;
        if (name == "chs")
            return ConflictHistorySearch;
        return std::nullopt;
    }

    // Build the brancher named by --branch: "dom-then-deg", or "dom-wdeg"
    // optionally suffixed with a scheme, e.g. "dom-wdeg:chs" (default ca.cd).
    auto brancher_from_string(const string & spec, const Problem & problem) -> optional<BranchHeuristic>
    {
        if (spec == "dom-then-deg")
            return branch_with(variable_order::dom_then_deg(problem), value_order::smallest_first());
        if (spec == "dom-wdeg" || spec.starts_with("dom-wdeg:")) {
            auto colon = spec.find(':');
            auto variant = (colon == string::npos) ? string{"ca.cd"} : spec.substr(colon + 1);
            auto scheme = scheme_from_string(variant);
            if (! scheme)
                return std::nullopt;
            return branch_with(variable_order::dom_wdeg(problem, *scheme), value_order::smallest_first());
        }
        return std::nullopt;
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Knapsack");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()                                                      //
            ("help", "Display help information")                                   //
            ("prove", "Create a proof")                                            //
            ("proof-files-basename", "Basename for the .opb and .pbp files",       //
                cxxopts::value<string>()->default_value("langford"))               //
            ("stats", "Print solve statistics")                                    //
            ("branch", "Branching heuristic: dom-then-deg, or dom-wdeg[:VARIANT] " //
                       "(VARIANT = classic / ia / ca / id / cd / ca.cd / chs)",    //
                cxxopts::value<string>()->default_value("dom-then-deg"))           //
            ("restart", "Restart on a Luby schedule with the given conflict scale " //
                        "(finds one solution only, since restarts cannot enumerate)", //
                cxxopts::value<unsigned long long>()->implicit_value("100"))       //
            ;

        options.add_options()                                                                   //
            ("size", "Size of the problem to solve", cxxopts::value<int>()->default_value("7")) //
            ("all", "Find all solutions");

        options.parse_positional({"size", "all"});
        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options] [size]", argv[0]);
        println("");
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    int k = options_vars["size"].as<int>();

    Problem p;
    vector<IntegerVariableID> position, solution;
    for (int i = 0; i < 2 * k; ++i) {
        position.emplace_back(p.create_integer_variable(0_i, Integer{2 * k - 1}));
        solution.emplace_back(p.create_integer_variable(1_i, Integer{k}));
    }

    p.post(AllDifferent{position});

    for (int i = 0; i < k; ++i) {
        auto i_var = p.create_integer_variable(Integer{i + 1}, Integer{i + 1});
        p.post(Element{i_var, position[i], &solution});
        p.post(Element{i_var, position[i + k], &solution});

        // position[i + k] = position[i] + i + 2
        p.post(PlusGAC{position[i + k], constant_variable(Integer{i + 2}), position[i]});
    }

    auto brancher = brancher_from_string(options_vars["branch"].as<string>(), p);
    if (! brancher) {
        println(cerr, "Error: unknown --branch value {}", options_vars["branch"].as<string>());
        return EXIT_FAILURE;
    }

    // Restarts re-explore, so without nogoods they can only find one solution;
    // when restarting we stop at the first, otherwise we enumerate as before.
    auto restarts = options_vars.contains("restart")
        ? make_optional(RestartSchedule::luby(options_vars["restart"].as<unsigned long long>()))
        : nullopt;
    auto keep_searching_after_solution = ! restarts.has_value();

    auto stats = solve_with(
        p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                println("solution: {}", solution | std::ranges::views::transform(cref(s)));
                println("position: {}", position | std::ranges::views::transform(cref(s)));
                println("");

                return keep_searching_after_solution;
            },
            .branch = *brancher,
            .restarts = restarts},
        options_vars.contains("prove")
            ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>())
            : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
