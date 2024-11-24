#include <cstdlib>
#include <gcs/constraints/regular.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <optional>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;
namespace po = boost::program_options;

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
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");         //

    po::options_description all_options{"All options"};

    all_options.add(display_options);

    po::variables_map options_vars;

    try {
        po::store(po::command_line_parser(argc, argv)
                      .options(all_options)
                      .run(),
            options_vars);
        po::notify(options_vars);
    }
    catch (const po::error & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
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
