/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/element.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::vector;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");

    po::options_description all_options{"All options"};
    all_options.add_options()                                                        //
        ("size", po::value<int>()->default_value(7), "Size of the problem to solve") //
        ("all", "Find all solutions");

    all_options.add(display_options);

    po::positional_options_description positional_options;
    positional_options
        .add("size", -1);

    po::variables_map options_vars;

    try {
        po::store(po::command_line_parser(argc, argv)
                      .options(all_options)
                      .positional(positional_options)
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

    int k = options_vars["size"].as<int>();

    Problem p = options_vars.contains("prove") ? Problem{ProofOptions{"langford.opb", "langford.veripb"}} : Problem{};
    vector<IntegerVariableID> position, solution;
    for (int i = 0; i < 2 * k; ++i) {
        position.emplace_back(p.create_integer_variable(0_i, Integer{2 * k - 1}));
        solution.emplace_back(p.create_integer_variable(1_i, Integer{k}));
    }

    p.post(AllDifferent{position});

    for (int i = 0; i < k; ++i) {
        auto i_var = p.create_integer_variable(Integer{i + 1}, Integer{i + 1});
        p.post(Element{i_var, position[i], solution});
        p.post(Element{i_var, position[i + k], solution});

        // position[i + k] = position[i] + i + 2
        p.post(Plus{position[i + k], constant_variable(Integer{i + 2}), position[i]});
    }

    auto stats = solve(p, [&](const CurrentState & state) -> bool {
        cout << "solution: ";
        for (auto & s : solution)
            cout << state(s) << " ";
        cout << endl;
        cout << "position: ";
        for (auto & s : position)
            cout << state(s) << " ";
        cout << endl;
        cout << endl;

        return true;
    });

    cout << stats;

    return EXIT_SUCCESS;
}
