#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <string>

#include <boost/program_options.hpp>

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
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");         //

    po::options_description all_options{"All options"};
    
    //    all_options.add_options()(
    //        "n", po::value<int>()->default_value(3), "Integer value n.") //
    //        ;
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

    //    auto n = options_vars["n"].as<int>();

    Problem p;

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "Solution:" << endl;
                return true;
            },
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>("failing_abs_test.opb", "failing_abs_test.veripb") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
