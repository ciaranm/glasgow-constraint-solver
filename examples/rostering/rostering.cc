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
    // This example is Example 2 from the paper
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

    if (options_vars.contains("help")) {
        cout << "Usage: " << argv[0] << " [options] [size]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    Problem p;
    vector<IntegerVariableID> day;
    day.emplace_back(p.create_integer_variable(0_i, 3_i, "day0"));
    day.emplace_back(p.create_integer_variable({1_i, 3_i}, "day1"));
    day.emplace_back(p.create_integer_variable({0_i, 2_i, 3_i}, "day2"));
    day.emplace_back(p.create_integer_variable({0_i, 1_i, 3_i}, "day3"));
    day.emplace_back(p.create_integer_variable({0_i}, "day4"));

    // Regular constraint for simple rostering problem
    // "Between 0s and 1s, 0s and 2s, or 1s and 2s, there should be at least one 3;
    // Furthermore, 0s followed by 3s followed by 2s is not allowed,
    // and neither are 1s followed by 3s followed by 0s
    // nor 2s followed by 3s followed by 1s"

    // 7 states 0..6, 4 possible values 0..3
    vector<vector<long>> transitions(7, vector<long>(4, -1));
    // Transitions
    transitions[0][0] = 1;
    transitions[0][1] = 2;
    transitions[0][2] = 3;
    transitions[0][3] = 0;

    transitions[1][0] = 1;
    transitions[1][3] = 4;

    transitions[2][1] = 2;
    transitions[2][3] = 5;

    transitions[3][2] = 3;
    transitions[3][3] = 6;

    transitions[4][3] = 4;
    transitions[4][0] = 1;
    transitions[4][1] = 2;

    transitions[5][3] = 5;
    transitions[5][1] = 2;
    transitions[5][2] = 3;

    transitions[6][3] = 6;
    transitions[6][2] = 3;
    transitions[6][0] = 1;

    auto regular = Regular{day, {0_i, 1_i, 2_i, 3_i}, 7, transitions, {0, 1, 2, 3, 4, 5, 6}};

    p.post(regular);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                for (const auto & var : day) {
                    cout << s(var);
                }
                cout << endl;
                return true;
            },
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>("rostering") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
