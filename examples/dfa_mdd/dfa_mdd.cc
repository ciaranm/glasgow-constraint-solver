#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <string>

#include <boost/program_options.hpp>
#include <gcs/constraints/mdd.hh>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{

    // Very simple MDD constraint representing the regular expression 0*1100*110*
    // As given as Example 1. in G. Gange, P.J. Stuckey, and R. Szymanek "MDD propagators with explanation"

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
    auto x = p.create_integer_variable_vector(7, 0_i, 1_i, "x");
    auto num_nodes = 18;
    vector<long> level{0, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 7};
    auto num_edges = 21;
    vector<long> from{0, 0, 1, 2, 2, 3, 4, 5, 6, 6, 7, 8, 9, 10, 10, 11, 12, 13, 14, 15, 16};
    vector<vector<Integer>> label{{1_i}, {0_i}, {1_i}, {1_i}, {0_i}, {0_i}, {1_i}, {1_i}, {1_i}, {0_i}, {0_i}, {1_i}, {1_i}, {1_i}, {0_i}, {0_i}, {0_i}, {1_i}, {1_i}, {0_i}, {1_i}};
    vector<long> to{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 11, 12, 13, 14, 14, 15, 15, 16, 17, 17};
    p.post(MDD{x, num_nodes, level, num_edges, from, label, to});
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "Solution:" << endl;
                return true;
            },
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>("dfa_mdd.opb", "dfa_mdd.veripb") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
