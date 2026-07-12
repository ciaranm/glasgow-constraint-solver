#include <gcs/constraints/equals.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <vector>

#include <cxxopts.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("N Queens Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")   //
            ("help", "Display help information") //
            ("prove", "Create a proof")          //
            ("branch",
                "Branching heuristic: default, or dom-wdeg[:VARIANT] "               //
                "(VARIANT = classic/ia/ca/id/cd/ca.cd/chs; bare = chs)",             //
                cxxopts::value<string>()->default_value("default"))                  //
            ("timeout", "Abort the solve after this many seconds (0 = no limit)",    //
                cxxopts::value<double>()->default_value("0"))                        //
            ("restarts", "Restart on a Luby schedule with the given conflict scale", //
                cxxopts::value<unsigned long long>()->implicit_value("100"));

        options.add_options()                                                                    //
            ("size", "Size of the problem to solve", cxxopts::value<int>()->default_value("88")) //
            ("all", "Find all solutions");

        options.parse_positional({"size"});
        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << "Usage: " << argv[0] << " [options] [size]" << endl;
        cout << endl;
        cout << options.help() << endl;
        return EXIT_SUCCESS;
    }

    cout << "Replicating the n-Queens benchmark." << endl;
    cout << "See Laurent D. Michel, Pierre Schaus, Pascal Van Hentenryck:" << endl;
    cout << "\"MiniCP: a lightweight solver for constraint programming.\"" << endl;
    cout << "Math. Program. Comput. 13(1): 133-184 (2021)." << endl;
    cout << "This should take 49339390 recursions with default options." << endl;
    cout << endl;

    int size = options_vars["size"].as<int>();
    Problem p;

    auto queens = p.create_integer_variable_vector(size, 0_i, Integer{size - 1}, "queen");

    for (int i = 0; i < size; ++i) {
        for (int j = i + 1; j < size; ++j) {
            p.post(NotEquals{queens[i], queens[j]});
            p.post(NotEquals{queens[i] + Integer{j - i}, queens[j]});
            p.post(NotEquals{queens[i] + -Integer{j - i}, queens[j]});
        }
    }

    auto restarts =
        options_vars.contains("restarts") ? make_optional(RestartSchedule::luby(options_vars["restarts"].as<unsigned long long>())) : nullopt;

    auto branch_spec = options_vars["branch"].as<string>();
    BranchHeuristic brancher;
    if (branch_spec == "default")
        brancher = branch_with(variable_order::dom(queens), value_order::smallest_in());
    else if (branch_spec == "dom-wdeg" || branch_spec.starts_with("dom-wdeg:")) {
        auto colon = branch_spec.find(':');
        auto scheme = bench::scheme_from_string(colon == string::npos ? "chs" : branch_spec.substr(colon + 1));
        if (! scheme) {
            cerr << "Error: unknown --branch scheme in " << branch_spec << endl;
            return EXIT_FAILURE;
        }
        brancher = branch_with(variable_order::dom_wdeg(p, *scheme), value_order::smallest_in());
    }
    else {
        cerr << "Error: unknown --branch value " << branch_spec << endl;
        return EXIT_FAILURE;
    }

    auto stats = bench::solve_with_timeout(options_vars["timeout"].as<double>(), p,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                           cout << "solution:";
                           for (auto & v : queens)
                               cout << " " << s(v);
                           cout << endl;

                           return options_vars.contains("all");
                       },
            .branch = brancher,
            .restarts = restarts},
        options_vars.contains("prove") ? make_optional<ProofOptions>("n_queens") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
