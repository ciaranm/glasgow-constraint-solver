/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/abs.hh>
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::pair;
using std::string;
using std::to_string;
using std::vector;

using namespace std::literals::string_literals;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");         //

    po::options_description all_options{"All options"};
    all_options.add_options()         //
        ("abs", "Use abs constraint") //
        ;

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

    if (options_vars.count("help")) {
        cout << "Usage: " << argv[0] << " [options] [size]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    Problem p = options_vars.count("prove") ? Problem{ProofOptions{"crystal_maze.opb", "crystal_maze.veripb"}} : Problem{};

    auto xs = p.create_integer_variable_vector(8, 1_i, 8_i, "box");
    p.post(AllDifferent{xs});
    p.branch_on(xs);

    vector<pair<int, int>> edges{{0, 1}, {0, 2}, {0, 3}, {0, 4},
        {1, 3}, {1, 4}, {1, 5}, {2, 3}, {2, 6}, {3, 4}, {3, 6},
        {3, 7}, {4, 5}, {4, 6}, {4, 7}, {5, 7}, {6, 7}};

    vector<IntegerVariableID> diffs, abs_diffs;
    for (auto & [x1, x2] : edges) {
        diffs.push_back(p.create_integer_variable(-7_i, 7_i, "diff" + to_string(x1) + "_" + to_string(x2)));
        if (options_vars.count("abs")) {
            abs_diffs.push_back(p.create_integer_variable(2_i, 7_i, "absdiff" + to_string(x1) + "_" + to_string(x2)));
            p.post(Abs{diffs.back(), abs_diffs.back()});
        }
        else {
            p.post(NotEquals{diffs.back(), 0_c});
            p.post(NotEquals{diffs.back(), 1_c});
            p.post(NotEquals{diffs.back(), -1_c});
        }

        p.post(Minus{xs[x1], xs[x2], diffs.back()});
    }

    auto stats = solve(p, [&](const CurrentState & s) -> bool {
        cout << "  " << s(xs[0]) << " " << s(xs[1]) << endl;
        cout << s(xs[2]) << " " << s(xs[3]) << " " << s(xs[4]) << " " << s(xs[5]) << endl;
        cout << "  " << s(xs[6]) << " " << s(xs[7]) << endl;
        cout << endl;
        return true;
    });

    cout << stats;

    return EXIT_SUCCESS;
}
