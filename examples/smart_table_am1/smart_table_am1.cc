#include <gcs/constraints/at_most_one.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/problem.hh>
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
    // A simple AtMost1 constraint example, using the encoding as a Smart Table
    // as given in "The Smart Table Constraint" Mairy, J. B., Deville, Y., & Lecoutre, C. (2015)
    //
    // Constrain that at most one out n variables can take the value n.
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");         //

    po::options_description all_options{"All options"};
    all_options.add_options()(
        "n", po::value<int>()->default_value(3), "Integer value n: at most 1 out n variables can take the value n.") //
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

    if (options_vars.contains("help")) {
        cout << "Usage: " << argv[0] << " [options] [size]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    auto n = options_vars["n"].as<int>();

    Problem p;
    auto vars = p.create_integer_variable_vector(n, 0_i, Integer{n}, "x");
    auto val = p.create_integer_variable(Integer{n}, Integer{n}, "y");

    p.post(AtMostOneSmartTable{vars, val});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "vars = [ ";
                for (const auto & var : vars) {
                    cout << s(var) << " ";
                }
                cout << "]" << endl;
                return true;
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>("smart_table_am1.opb", "smart_table_am1.pbp") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
