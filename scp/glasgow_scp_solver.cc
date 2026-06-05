#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/scp_reader.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include <map>
#include <string>

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
using std::ifstream;
using std::istreambuf_iterator;
using std::make_optional;
using std::map;
using std::nullopt;
using std::string;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

// Workflow 3: solve a problem given as a `.scp` (s-expression CP) file. The
// .scp is the *input* (e.g. produced by another solver's --prove, or by a
// higher-level translator), and with --prove the run emits a proof that, via
// cake_pb_cp, is verified against that same .scp. See gcs/scp_reader.hh.
auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("glasgow_scp_solver", "Solve a .scp (s-expression CP) problem");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()                                                //
            ("help", "Display help information")                             //
            ("prove", "Create a proof")                                      //
            ("proof-files-basename", "Basename for the .opb and .pbp files", //
                cxxopts::value<string>()->default_value("scp"))              //
            ("all", "Find all solutions rather than just the first")         //
            ("stats", "Print solve statistics")                              //
            ("file", "The .scp file to solve", cxxopts::value<string>())     //
            ;
        options.parse_positional({"file"});
        options.positional_help("scp-file.scp");
        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help") || ! options_vars.contains("file")) {
        println("Usage: {} [options] scp-file.scp", argv[0]);
        cout << options.help() << std::endl;
        return options_vars.contains("help") ? EXIT_SUCCESS : EXIT_FAILURE;
    }

    auto file_name = options_vars["file"].as<string>();
    ifstream infile{file_name};
    if (! infile) {
        println(cerr, "Error: could not open '{}'", file_name);
        return EXIT_FAILURE;
    }
    string text{istreambuf_iterator<char>{infile}, istreambuf_iterator<char>{}};

    Problem problem;
    map<string, IntegerVariableID> variables;
    try {
        variables = read_scp(problem, text);
    }
    catch (const std::exception & e) {
        println(cerr, "Error: {}", e.what());
        return EXIT_FAILURE;
    }

    bool find_all = options_vars.contains("all");
    auto stats = solve_with(problem,
        SolveCallbacks{
            .solution = [&](const CurrentState & state) -> bool {
                for (const auto & [name, id] : variables)
                    print("{}={} ", name, state(id));
                println("");
                return find_all;
            }},
        options_vars.contains("prove")
            ? make_optional<ProofOptions>(ProofFileNames{options_vars["proof-files-basename"].as<string>()}, true, false)
            : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
