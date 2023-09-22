#include <gcs/constraints/knapsack.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::vector;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");

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

    Problem p;
    auto items = p.create_integer_variable_vector(6, 0_i, 1_i, "item");
    auto profit = p.create_integer_variable(6_i, 10_i, "profit");
    auto weight = p.create_integer_variable(5_i, 7_i, "weight");

    vector<Integer> weights = {2_i, 5_i, 2_i, 3_i, 2_i, 3_i};
    vector<Integer> profits = {2_i, 4_i, 2_i, 5_i, 4_i, 3_i};

    auto oddity = p.create_integer_variable(0_i, 20_i, "oddity");
    p.post(LinearEquality{WeightedSum{} + 1_i * profit + -2_i * oddity, 1_i, true});

    p.post(WeightedSum{} + 1_i * items[5] == 0_i);

    p.post(Knapsack{weights, profits, items, weight, profit});
    p.maximise(profit);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "solution:";
                for (auto & v : items)
                    cout << " " << s(v);
                cout << " profit " << s(profit) << " weight " << s(weight) << endl;

                return true;
            },
            .branch = branch_on_dom_then_deg(items)},
        options_vars.contains("prove") ? make_optional<ProofOptions>("knapsack.opb", "knapsack.veripb") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
