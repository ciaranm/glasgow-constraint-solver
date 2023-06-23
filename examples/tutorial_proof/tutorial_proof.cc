#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
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
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

using namespace std::literals::string_literals;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()                                 //
        ("help", "Display help information")                      //
        ("prove", "Create a proof")                               //
        ("full-proof-encoding", "Use the longer proof encoding"); //

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

    Problem p;

    auto va = p.create_integer_variable(1_i, 5_i, "a");
    auto vb = p.create_integer_variable(1_i, 2_i, "b");
    auto vc = p.create_integer_variable(2_i, 3_i, "c");
    auto vd = p.create_integer_variable(2_i, 3_i, "d");
    p.post(AllDifferent({va, vb, vc, vd}));
    p.post(LinearLessEqual{Linear{{1_i, va}, {1_i, vb}, {1_i, vc}}, 9_i});

    auto obj = p.create_integer_variable(0_i, 10000_i, "obj");
    p.post(LinearEquality{Linear{{2_i, va}, {3_i, vd}, {-1_i, obj}}, 0_i});

    p.minimise(obj);
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "a = " << s(va) << " b = " << s(vb) << " c = " << s(vc)
                     << " d = " << s(vd) << " obj = " << s(obj) << endl;
                return true;
            },
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>(
                                             "tutorial_proof.opb", "tutorial_proof.veripb", true, options_vars.count("full-proof-encoding"))
                                       : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}