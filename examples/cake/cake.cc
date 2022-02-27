/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/linear_equality.hh>
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
using std::string;
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
        cout << "Usage: " << argv[0] << " [options]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    Problem p = options_vars.contains("prove") ? Problem{ProofOptions{"cake.opb", "cake.veripb"}} : Problem{};

    // https://www.minizinc.org/doc-2.5.5/en/modelling.html#an-arithmetic-optimisation-example
    auto banana = p.create_integer_variable(0_i, 100_i);
    auto chocolate = p.create_integer_variable(0_i, 100_i);
    p.post(LinearLessEqual{Linear{{250_i, banana}, {200_i, chocolate}}, 4000_i});
    p.post(LinearLessEqual{Linear{{2_i, banana}}, 6_i});
    p.post(LinearLessEqual{Linear{{75_i, banana}, {150_i, chocolate}}, 2000_i});
    p.post(LinearLessEqual{Linear{{100_i, banana}, {150_i, chocolate}}, 500_i});
    p.post(LinearLessEqual{Linear{{75_i, chocolate}}, 500_i});

    auto profit = p.create_integer_variable(0_i, 107500_i, "profit");
    p.post(LinearEquality{Linear{{400_i, banana}, {450_i, chocolate}, {-1_i, profit}}, 0_i});

    p.branch_on(vector<IntegerVariableID>{banana, chocolate});
    p.maximise(profit);
    auto stats = solve(p, [&](const CurrentState & s) -> bool {
        cout << "banana cakes = " << s(banana) << ", chocolate cakes = "
             << s(chocolate) << ", profit = " << s(profit) << endl;
        return true;
    });

    cout << stats;

    return EXIT_SUCCESS;
}
