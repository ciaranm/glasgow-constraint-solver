#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/scp_reader.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
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
//
// A `(prob_type (minimize V))` / `(maximize V)` document is solved as the
// optimisation problem it says it is, so `--prove` on one yields an
// optimisation proof rather than an enumeration of every feasible solution.
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
            ("all", "Find all solutions (implied by an objective)")          //
            ("parse-only",
                "Read the file and post its constraints, but do "
                "not search: a cheap check that the .scp is one "
                "this solver can rebuild")                               //
            ("stats", "Print solve statistics")                          //
            ("file", "The .scp file to solve", cxxopts::value<string>()) //
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
    ScpModel model;
    try {
        model = read_scp(problem, text);
    }
    catch (const ScpUnsupportedConstraintError & e) {
        // Distinguished from every other read failure by its exit status, so a
        // caller checking writer/reader symmetry can tell "this reader has no
        // case for that keyword" (a gap to fix) from "this reader knows the
        // keyword but cannot rebuild this instance" (a view operand, say --- a
        // documented limitation). See run_test_and_verify.bash.
        println(cerr, "Error: {}", e.what());
        return 2;
    }
    catch (const std::exception & e) {
        println(cerr, "Error: {}", e.what());
        return EXIT_FAILURE;
    }

    // --parse-only stops here: read_scp has created the variables and posted
    // every constraint, which is the whole question when the caller is checking
    // that a written .scp can be read back (run_test_and_verify.bash does this
    // for every proving example, so an unreadable keyword is caught by the
    // example that writes it rather than by a chain run much later).
    if (options_vars.contains("parse-only"))
        return EXIT_SUCCESS;

    // read_scp resolves an objective but leaves posting it to us, so that a
    // caller who wants to enumerate an optimisation instance still can. Here we
    // honour it: the .scp says what problem it is, and solving something else
    // would be answering a different question.
    if (model.minimise_variable)
        problem.minimise(*model.minimise_variable);

    // With an objective, every solution is just the next bound on the way to
    // the optimum, so the search must run to completion however --all is set;
    // the last solution printed is the optimal one.
    bool find_all = options_vars.contains("all") || model.minimise_variable.has_value();
    auto stats = solve_with(problem, //
        SolveCallbacks{              //
            .solution = [&](const CurrentState & state) -> bool {
                for (const auto & [name, id] : model.variables)
                    print("{}={} ", name, state(id));
                println("");
                return find_all;
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>(ProofFileNames{options_vars["proof-files-basename"].as<string>()}) : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
