#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <string>

#include <boost/program_options.hpp>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/inverse.hh>

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
    po::options_description display_options{"Program options"};
    display_options.add_options()("help", "Display help information")("prove", "Create a proof");

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

    int n = 30; // Size of the permutation

    Problem p;
    auto perm = p.create_integer_variable_vector(n, 1_i, Integer(n), "perm");
    auto inv_perm = p.create_integer_variable_vector(n, 1_i, Integer(n), "inv_perm");

    // Enforce inverse relationship: if perm[i] = j, then inv_perm[j] = i
    p.post(Inverse{perm, inv_perm, 1_i, 1_i, LPJustificationOptions{}});
    for (int i = 0; i < n - 2; i++) {
        p.post(LessThan{perm[i], perm[i + 2]});
    }

    p.post(Equals{perm[3], 2_c});
    p.post(Equals{perm[6], 8_c});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "Solution:" << endl;
                for (int i = 0; i < n; i++) {
                    cout << "perm[" << i + 1 << "] = " << s(perm[i]) << ", ";
                    cout << "inv_perm[" << i + 1 << "] = " << s(inv_perm[i]) << endl;
                }
                return false;
            },
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>("cheese") : nullopt);

    cout << stats;

    return test_innards::run_veripb("cheese.opb", "cheese.pbp");
    ;
}