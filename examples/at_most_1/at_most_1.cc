#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/extensional.hh>
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
    // Smart table representation of the AtMost1 constraint
    // As given in "The Smart Table Constraint" Mairy, J. B., Deville, Y., & Lecoutre, C. (2015)
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
    auto x = p.create_integer_variable_vector(n, 0_i, Integer{n}, "x");
    auto y = p.create_integer_variable(Integer{n}, Integer{n}, "y");


    // Build the smart table
    SmartTuples tuples;

    for (int i = 0; i < n; ++i) {
        vector<SmartEntry> tuple;
        for (int j = 0; j < n; ++j) {
            if (j != i) {
                tuple.emplace_back(SmartTable::not_equals(x[j], y));
            }
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = x;
    all_vars.emplace_back(y);

    p.post(SmartTable{all_vars, tuples});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "x = [ ";
                for (const auto & var : x) {
                    cout << s(var) << " ";
                }
                cout << "]" << endl;
                return true;
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>("at_most_1.opb", "at_most_1.veripb") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
