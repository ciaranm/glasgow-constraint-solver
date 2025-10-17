#include <cstdlib>
#include <gcs/constraints/regular.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
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
using std::vector;

auto main(int argc, char * argv[]) -> int
{

    // This example is Example 1 from the paper
    // "A Regular Language Membership Constraint for Finite Sequences of Variables"
    // G. Pesant 2004
    cxxopts::Options options("Regex Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")
            ("help", "Display help information")
            ("prove", "Create a proof");

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    Problem p;
    auto x = p.create_integer_variable_vector(5, 0_i, 2_i, "x");

    // Regular constraint for the language given by 00*11*00* + 2*
    // 5 states 0..4, 3 possible values 0..2
    vector<vector<long>> transitions(5, vector<long>(3, -1));
    // Transitions
    transitions[0][0] = 1;
    transitions[0][2] = 4;
    transitions[1][0] = 1;
    transitions[1][1] = 2;
    transitions[2][1] = 2;
    transitions[2][0] = 3;
    transitions[3][0] = 3;
    transitions[4][2] = 4;

    auto regular = Regular{x, {0_i, 1_i, 2_i}, 5, transitions, {3, 4}};

    p.post(regular);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                for (const auto & var : x) {
                    cout << s(var);
                }
                cout << endl;
                return true;
            },
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>("regex") : nullopt);

    cout << stats;

    //    system("veripb --trace --useColor regex.opb regex.pbp");
    return EXIT_SUCCESS;
}
