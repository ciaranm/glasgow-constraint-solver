#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <string>

#include <boost/program_options.hpp>
#include <gcs/constraints/smart_table.hh>

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

    //    Tree 0(1 nodes): x[2] < 1;  Tree 1(1 nodes): x[3] != 1;  Tree 2(1 nodes): x[1] > 0;  Tree 3(1 nodes): x[0] == 1;  x[3] in {3, 1, 2, -1};  x[2] notin {2, 0};  x[1] > 1;  x[2] == 0;
    //    Tree 0(1 nodes): x[3] >= 1;  Tree 1(1 nodes): x[2] in {0, 3, 1};  x[3] in {4, 1};  x[3] == 2;
    //    Tree 0(2 nodes): x[1] == x[0];  Tree 1(1 nodes): x[3] <= 2;  Tree 2(1 nodes): x[2] < 3;  x[3] < 0;  x[1] in {3, -1, 2};  x[1] > 3;  x[0] notin {0, 1};

    auto x = p.create_integer_variable_vector(4, -1_i, 4_i);

    auto tuples = SmartTuples{
        {SmartTable::less_than(x[2], 1_i), SmartTable::not_equals(x[3], 1_i), SmartTable::greater_than(x[1], 0_i), SmartTable::equals(x[0], 1_i),
            SmartTable::in_set(x[3], {3_i, 1_i, 2_i, -1_i}), SmartTable::not_in_set(x[2], {2_i, 0_i}), SmartTable::greater_than(x[1], 1_i), SmartTable::equals(x[2], 0_i)},

        {SmartTable::greater_than_equal(x[3], 1_i), SmartTable::in_set(x[2], {0_i, 3_i, 1_i}), SmartTable::in_set(x[3], {4_i, 1_i}), SmartTable::equals(x[3], 2_i)},

        {SmartTable::equals(x[1], x[0]), SmartTable::less_than_equal(x[3], 2_i), SmartTable::less_than(x[2], 3_i), SmartTable::less_than(x[3], 0_i), SmartTable::in_set(x[1], {3_i, -1_i, 2_i}),
            SmartTable::greater_than(x[1], 3_i), SmartTable::not_in_set(x[0], {0_i, 1_i})}};

    p.post(SmartTable{x, tuples});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool {
                cout << "Solution:" << endl;
                return true;
            },
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>("consolidate_unary.opb", "consolidate_unary.veripb") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
