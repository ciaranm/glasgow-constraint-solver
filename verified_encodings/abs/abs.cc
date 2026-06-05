#include <gcs/constraints/abs.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
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

// A deliberately tiny model used to exercise the *verified-encoding* workflow
// end to end: the solver writes a .scp alongside the .opb/.pbp, and the chain
//
//     cake_pb_cp abs.scp > abs.verifiedopb
//     veripb abs.verifiedopb abs.pbp --elaborate abs.corepb
//     cake_pb_cp abs.scp abs.corepb
//
// re-derives the OPB from the .scp with the CakeML-verified encoder and checks
// the elaborated proof against it. abs is the first constraint whose solver
// encoding lines up with cake_pb_cp's (see the encoding spec repo), so it is the
// bootstrap of the verified_encodings/ family. See ../run_cake_pb_cp.bash.
auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("abs (verified-encoding demo)");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options()                                                //
            ("help", "Display help information")                             //
            ("prove", "Create a proof")                                      //
            ("proof-files-basename", "Basename for the .opb and .pbp files", //
                cxxopts::value<string>()->default_value("abs"))              //
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
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    Problem p;

    // Deliberately UNSAT: Y = |X| forces Y in [0, 3], but Y is declared in
    // [4, 5], so there is no solution. X spans both signs, so the abs sign bit
    // is genuinely exercised. An UNSAT refutation avoids solution-logging
    // (solx) steps, which the workflow-2 chain cannot yet verify against a
    // cake_pb_cp OPB because cake emits no `preserved:` line (see the encoding
    // spec repo / dev_docs — a documented cake limitation to lift later).
    //
    // Named CP variables are upper-case by convention (the PB variables they
    // encode to, e.g. i[X][sign], are lower-case); only auto-numbered _N
    // names are the exception.
    auto x = p.create_integer_variable(-3_i, 3_i, "X");
    auto y = p.create_integer_variable(4_i, 5_i, "Y");
    p.post(Abs{x, y}); // Y = |X|

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                println("X = {}, Y = {}", s(x), s(y));
                return true;
            }},
        options_vars.contains("prove")
            ? make_optional<ProofOptions>(ProofFileNames{options_vars["proof-files-basename"].as<string>()}, true, false)
            : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
