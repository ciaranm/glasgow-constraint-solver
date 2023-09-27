
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <string>

#include <boost/program_options.hpp>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/constraints/in.hh>

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

    auto x = p.create_integer_variable_vector(8, 0_i, 7_i);

    p.post(In{x[0], {1_i, 2_i, 3_i}});
    p.post(In{x[1], {3_i, 2_i}});
    p.post(In{x[2], {1_i, 3_i}});
    p.post(In{x[3], {2_i, 1_i}});

    p.post(In{x[4], {5_i, 6_i}});
    p.post(In{x[5], {7_i, 4_i}});
    p.post(In{x[6], {5_i, 7_i}});
    p.post(In{x[7], {4_i, 6_i}});

    p.post(CircuitSCC{x});
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool {
                cout << "Solution:" << endl;
                return true;
            },
        },
        /*options_vars.contains("prove") ? */ make_optional<ProofOptions>("disconnected.opb", "disconnected.veripb") /*: nullopt*/);

    cout << stats;

    system("veripb --trace --useColor disconnected.opb disconnected.veripb");
    return EXIT_SUCCESS;
}
