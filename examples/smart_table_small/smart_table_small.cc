#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/extensional.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

namespace po = boost::program_options;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    // A small, manually specified Smart Table example. This is the fully worked example
    // from "Proof Logging for Smart Extensional Constraints" M. J. McIlree, and C. McCreesh (2023)

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

    auto A = p.create_integer_variable(1_i, 3_i, "A");
    auto B = p.create_integer_variable(1_i, 3_i, "B");
    auto C = p.create_integer_variable(1_i, 3_i, "C");

    auto tuples = SmartTuples{
        {SmartTable::less_than(A, B), SmartTable::in_set(A, {1_i, 2_i}), SmartTable::equals(C, 3_i)},
        {SmartTable::equals(A, B), SmartTable::not_equals(A, 1_i), SmartTable::greater_than_equal(B, C)}};
    p.post(SmartTable{{A, B, C}, tuples});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "A = " << s(A) << " B = " << s(B) << " C = " << s(C) << endl;
                return true;
            }},
        ProofOptions{"smart_table_small"});

    cout << stats;

    return EXIT_SUCCESS;
}
