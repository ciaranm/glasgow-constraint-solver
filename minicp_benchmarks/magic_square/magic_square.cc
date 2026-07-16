/* vim : set sw = 4 sts = 4 et foldmethod = syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>

#include <cxxopts.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::ifstream;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Magic Square");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")   //
            ("help", "Display help information") //
            ("prove", "Create a proof")          //
            ("branch",
                "Branching heuristic: default, or dom-wdeg[:VARIANT] "                                               //
                "(VARIANT = classic/ia/ca/id/cd/ca.cd/chs; bare = chs)",                                             //
                cxxopts::value<std::string>()->default_value("default"))                                             //
            ("timeout", "Abort the solve after this many seconds (0 = no limit)",                                    //
                cxxopts::value<double>()->default_value("0"))                                                        //
            ("restarts", "Restart on a Luby schedule with the given conflict scale",                                 //
                cxxopts::value<unsigned long long>()->implicit_value("100"))                                         //
            ("all-different", "All-different encoding to use: 'gac', 'vc', or 'not-equals' (the not-equals clique)", //
                cxxopts::value<std::string>()->default_value("not-equals"));

        options.add_options()("size", "Size of the problem to solve", cxxopts::value<int>()->default_value("5"));

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

    const string all_different_mode = options_vars["all-different"].as<string>();
    if (all_different_mode != "gac" && all_different_mode != "vc" && all_different_mode != "not-equals") {
        cerr << "Error: --all-different must be 'gac', 'vc', or 'not-equals'." << endl;
        return EXIT_FAILURE;
    }

    cout << "Replicating the MiniCP Magic Square benchmark." << endl;
    cout << "See Laurent D. Michel, Pierre Schaus, Pascal Van Hentenryck:" << endl;
    cout << "\"MiniCP: a lightweight solver for constraint programming.\"" << endl;
    cout << "Math. Program. Comput. 13(1): 133-184 (2021)." << endl;
    cout << "This should take 6042079 recursions with default options." << endl;
    cout << endl;

    int size = options_vars["size"].as<int>();
    Problem p;
    Integer m{size * (size * size + 1) / 2};

    vector<vector<IntegerVariableID>> grid;
    vector<IntegerVariableID> grid_flat;
    for (int x = 0; x < size; ++x) {
        grid.emplace_back();
        for (int y = 0; y < size; ++y) {
            auto var = p.create_integer_variable(1_i, Integer{size * size});
            grid[x].push_back(var);
            grid_flat.push_back(var);
        }
    }

    // As far as I can tell, the statistics reported in the paper only make
    // sense for non-GAC all-different (the 'vc' or 'not-equals' encodings,
    // which do the same pruning as each other).
    if (all_different_mode == "gac") {
        p.post(AllDifferent{grid_flat});
    }
    else if (all_different_mode == "vc") {
        p.post(AllDifferent{grid_flat} //
                .with_consistency(consistency::VC{}));
    }
    else {
        for (unsigned x = 0; x < grid_flat.size(); ++x)
            for (unsigned y = x + 1; y < grid_flat.size(); ++y)
                p.post(NotEquals{grid_flat[x], grid_flat[y]});
    }

    for (int x = 0; x < size; ++x) {
        WeightedSum coeff_vars;
        for (int y = 0; y < size; ++y)
            coeff_vars += 1_i * grid[x][y];
        p.post(move(coeff_vars) == m);
    }

    for (int y = 0; y < size; ++y) {
        WeightedSum coeff_vars;
        for (int x = 0; x < size; ++x)
            coeff_vars += 1_i * grid[x][y];
        p.post(move(coeff_vars) == m);
    }

    WeightedSum coeff_vars1, coeff_vars2;
    for (int xy = 0; xy < size; ++xy) {
        coeff_vars1 += 1_i * grid[xy][xy];
        coeff_vars2 += 1_i * grid[size - xy - 1][xy];
    }
    p.post(move(coeff_vars1) == m);
    p.post(move(coeff_vars2) == m);

    p.post(LessThan{grid[0][size - 1], grid[size - 1][0]});
    p.post(LessThan{grid[0][0], grid[size - 1][size - 1]});
    p.post(LessThan{grid[0][0], grid[size - 1][0]});

    auto restarts =
        options_vars.contains("restarts") ? make_optional(RestartSchedule::luby(options_vars["restarts"].as<unsigned long long>())) : nullopt;

    auto branch_spec = options_vars["branch"].as<std::string>();
    BranchHeuristic brancher;
    if (branch_spec == "default")
        brancher = branch_with(variable_order::dom(grid_flat), value_order::smallest_in());
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

    unsigned long long n_solutions = 0;
    auto stats = bench::solve_with_timeout(options_vars["timeout"].as<double>(), p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return ++n_solutions < 10000; }, .branch = brancher, .restarts = restarts},
        options_vars.contains("prove") ? make_optional<ProofOptions>("magic_square") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
