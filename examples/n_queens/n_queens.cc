/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <util/for_each.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::string;
using std::vector;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");

    po::options_description all_options{"All options"};
    all_options.add_options()                                                         //
        ("size", po::value<int>()->default_value(88), "Size of the problem to solve") //
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

    cout << "Replicating the n-Queens benchmark." << endl;
    cout << "See Laurent D. Michel, Pierre Schaus, Pascal Van Hentenryck:" << endl;
    cout << "\"MiniCP: a lightweight solver for constraint programming.\"" << endl;
    cout << "Math. Program. Comput. 13(1): 133-184 (2021)." << endl;
    cout << "This should take 49339390 recursions with default options." << endl;
    cout << endl;

    int size = options_vars["size"].as<int>();
    Problem p = options_vars.contains("prove") ? Problem{ProofOptions{"n_queens.opb", "n_queens.veripb"}} : Problem{};

    auto queens = p.create_integer_variable_vector(size, 0_i, Integer{size - 1}, "queen");

    for (int i = 0; i < size; ++i) {
        for (int j = i + 1; j < size; ++j) {
            p.post(NotEquals{queens[i], queens[j]});
            p.post(NotEquals{queens[i] + Integer{j - i}, queens[j]});
            p.post(NotEquals{queens[i] + -Integer{j - i}, queens[j]});
        }
    }

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "solution:";
                for (auto & v : queens)
                    cout << " " << s(v);
                cout << endl;

                return options_vars.contains("all");
            },
            .guess = [&](const CurrentState & state, IntegerVariableID var) -> vector<Literal> {
                return vector<Literal>{var == state.lower_bound(var), var != state.lower_bound(var)};
            }});

    cout << stats;

    return EXIT_SUCCESS;
}
