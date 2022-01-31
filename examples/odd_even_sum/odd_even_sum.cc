/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::string;

using namespace std::literals::string_literals;

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

    if (options_vars.count("help")) {
        cout << "Usage: " << argv[0] << " [options]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    Problem p = options_vars.count("prove")
        ? Problem{Proof{"odd_even_sum.opb", "odd_even_sum.veripb"}}
        : Problem{};

    auto a = p.create_integer_variable(0_i, 5_i, "a");
    auto b = p.create_integer_variable(0_i, 5_i, "b");
    auto c = p.create_integer_variable(0_i, 5_i, "c");
    auto d = p.create_integer_variable(0_i, 10_i, "d");
    auto e = p.create_integer_variable(0_i, 2_i, "e");

    p.post(LinearEquality{Linear{{2_i, a}, {2_i, b}, {2_i, c}, {-2_i, d}, {1_i, e}}, 1_i, true});

    auto stats = solve(p, [&](const CurrentState & s) -> bool {
        cout << s(a) << " " << s(b) << " " << s(c) << " " << s(d) << " " << s(e) << endl;
        return true;
    });

    cout << stats;

    return EXIT_SUCCESS;
}
