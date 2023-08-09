#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <string>

#include <boost/program_options.hpp>
#include <gcs/constraints/circuit/circuit.hh>

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

    auto x = p.create_integer_variable_vector(4, 0_i, 3_i);

    p.post(CircuitSCC{x});
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "Solution:" << endl;
                cout << s(x[0]) << " " << s(x[1]) << " " << s(x[2]) << " " << s(x[3]) << endl;
                return true;
            },
        } /*,make_optional<ProofOptions>("micro_circuit.opb", "micro_circuit.veripb")*/);

    cout << stats;

    return EXIT_SUCCESS;
}
