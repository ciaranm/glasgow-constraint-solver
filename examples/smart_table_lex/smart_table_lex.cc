#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/lex.hh>
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
    // A simple Lex constraint example, using the encoding as a Smart Table
    // as given in "The Smart Table Constraint" Mairy, J. B., Deville, Y., & Lecoutre, C. (2015)
    //
    // x = [5, 2, ?, 6], y = [5, 2, 10, 5] with x >lex y means ? = 10
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

    int n = 4;
    Problem p;
    auto x = p.create_integer_variable_vector(n, 0_i, 10_i, "x");
    auto y = p.create_integer_variable_vector(n, 0_i, 10_i, "y");

    p.post(Equals(y[0], 5_c));
    p.post(Equals(y[1], 2_c));
    p.post(Equals(y[2], 10_c));
    p.post(Equals(y[3], 5_c));

    p.post(Equals(x[0], 5_c));
    p.post(Equals(x[1], 2_c));
    // Only option for x[2] is 10, since it comes lexicographically after
    p.post(Equals(x[3], 6_c));

    p.post(LexSmartTable{x, y});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "x = [ ";
                for (const auto & var : x) {
                    cout << s(var) << " ";
                }
                cout << "]" << endl;
                cout << "y = [ ";
                for (const auto & var : y) {
                    cout << s(var) << " ";
                }
                cout << "]\n"
                     << endl;
                return true;
            }},
        ProofOptions{"lex.opb", "lex.veripb"});

    cout << stats;

    return EXIT_SUCCESS;
}
