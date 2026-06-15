#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>

#include <cstdlib>
#include <cxxopts.hpp>
#include <fstream>
#include <iostream>
#include <vector>

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
using std::ifstream;
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
    cxxopts::Options options("Ortho_latin Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                       //
            ("help", "Display help information")                                     //
            ("prove", "Create a proof")                                              //
            ("proof-files-basename", "Basename for the .opb and .pbp files",         //
                cxxopts::value<string>()->default_value("ortho_latin"))              //
            ("stats", "Print solve statistics")                                      //
            ("branch", "Branching heuristic: default, or dom-wdeg[:VARIANT] "        //
                       "(VARIANT = classic/ia/ca/id/cd/ca.cd/chs; bare = chs)",      //
                cxxopts::value<string>()->default_value("default"))                  //
            ("timeout", "Abort the solve after this many seconds (0 = no limit)",    //
                cxxopts::value<double>()->default_value("0"))                        //
            ("restarts", "Restart on a Luby schedule with the given conflict scale", //
                cxxopts::value<unsigned long long>()->implicit_value("100"))         //
            ;

        options.add_options()                                                                    //
            ("size", "Size of the problem to solve", cxxopts::value<int>()->default_value("88")) //
            ("all", "Find all solutions");

        options.parse_positional({"size"});

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

    auto restarts = options_vars.contains("restarts")
        ? make_optional(RestartSchedule::luby(options_vars["restarts"].as<unsigned long long>()))
        : nullopt;

    auto branch_spec = options_vars["branch"].as<string>();
    BranchHeuristic brancher;
    if (branch_spec == "default")
        brancher = branch_with(variable_order::dom_then_deg(p), value_order::smallest_first());
    else if (branch_spec == "dom-wdeg" || branch_spec.starts_with("dom-wdeg:")) {
        auto colon = branch_spec.find(':');
        auto scheme = bench::scheme_from_string(colon == string::npos ? "chs" : branch_spec.substr(colon + 1));
        if (! scheme) {
            println(cerr, "Error: unknown --branch scheme in {}", branch_spec);
            return EXIT_FAILURE;
        }
        brancher = branch_with(variable_order::dom_wdeg(p, *scheme), value_order::smallest_first());
    }
    else {
        println(cerr, "Error: unknown --branch value {}", branch_spec);
        return EXIT_FAILURE;
    }

    auto stats = bench::solve_with_timeout(options_vars["timeout"].as<double>(), p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                for (int x = 0; x < size; ++x) {
                    for (int y = 0; y < size; ++y)
                        print("{},{} ", s(g1[x][y]), s(g2[x][y]));
                    println("");
                }
                println("");

                return true;
            },
            .branch = brancher,
            .restarts = restarts},
        options_vars.contains("prove")
            ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>())
            : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
