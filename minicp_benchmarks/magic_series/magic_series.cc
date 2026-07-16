#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>

#include <cstdlib>
#include <cxxopts.hpp>
#include <iostream>
#include <optional>
#include <util/enumerate.hh>
#include <vector>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Magic Series Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")   //
            ("help", "Display help information") //
            ("prove", "Create a proof")          //
            ("branch",
                "Branching heuristic: default, or dom-wdeg[:VARIANT] "               //
                "(VARIANT = classic/ia/ca/id/cd/ca.cd/chs; bare = chs)",             //
                cxxopts::value<std::string>()->default_value("default"))             //
            ("timeout", "Abort the solve after this many seconds (0 = no limit)",    //
                cxxopts::value<double>()->default_value("0"))                        //
            ("restarts", "Restart on a Luby schedule with the given conflict scale", //
                cxxopts::value<unsigned long long>()->implicit_value("100"))         //
            ("extra-constraints", "Use extra constraints described in the MiniCP paper");

        options.add_options() //
            ("size", "Size of the problem to solve", cxxopts::value<int>()->default_value("300"));

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

    cout << "Replicating the MiniCP Magic Series benchmark." << endl;
    cout << "See Laurent D. Michel, Pierre Schaus, Pascal Van Hentenryck:" << endl;
    cout << "\"MiniCP: a lightweight solver for constraint programming.\"" << endl;
    cout << "Math. Program. Comput. 13(1): 133-184 (2021)." << endl;
    cout << "This should take 1193 recursions with default options." << endl;
    cout << endl;

    int size = options_vars["size"].as<int>();
    Problem p;

    auto series = p.create_integer_variable_vector(size, 0_i, Integer{size - 1}, "series");

    for (int i = 0; i < size; ++i) {
        WeightedSum coeff_vars;
        for (int j = 0; j < size; ++j) {
            auto series_j_eq_i = p.create_integer_variable(0_i, 1_i);
            p.post(EqualsIff{series[j], constant_variable(Integer{i}), series_j_eq_i == 1_i});
            coeff_vars += 1_i * series_j_eq_i;
        }

        p.post(move(coeff_vars) == 1_i * series[i]);
    }

    WeightedSum sum_s;
    for (auto & s : series)
        sum_s += 1_i * s;
    p.post(move(sum_s) == Integer{size});

    // Although this is discussed in the text, it isn't included in the executed
    // benchmarks.
    if (options_vars.contains("extra-constraints")) {
        WeightedSum sum_mul_s;
        for (const auto & [idx, s] : enumerate(series))
            sum_mul_s += Integer(idx) * s;
        p.post(move(sum_mul_s) == Integer{size});
    }

    auto restarts =
        options_vars.contains("restarts") ? make_optional(RestartSchedule::luby(options_vars["restarts"].as<unsigned long long>())) : nullopt;

    auto branch_spec = options_vars["branch"].as<std::string>();
    BranchHeuristic brancher;
    if (branch_spec == "default")
        brancher = branch_with(variable_order::dom(series), value_order::smallest_in());
    else if (branch_spec == "dom-wdeg" || branch_spec.starts_with("dom-wdeg:")) {
        auto colon = branch_spec.find(':');
        auto scheme = bench::scheme_from_string(colon == std::string::npos ? "chs" : branch_spec.substr(colon + 1));
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
                           for (auto & v : series)
                               cout << " " << s(v);
                           cout << endl;

                           return true;
                       },
            .branch = brancher,
            .restarts = restarts},
        options_vars.contains("prove") ? make_optional<ProofOptions>("magic_series") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
