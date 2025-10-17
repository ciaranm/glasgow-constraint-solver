#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <string>

#include <cxxopts.hpp>
#include <gcs/constraints/smart_table.hh>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;


auto main(int argc, char * argv[]) -> int
{
    /**
     * This example was created from a failing Random Smart Table test, showing the need for consolidating unary entries
     * e.g. X1 < 3; X1 < 5 in the same tuple should be combined to just X1 < 3 in the PB encoding otherwise we can get
     * unsupported values that don't unit propagate in the proof.
     *
     * See issue SmartTableRandom failure #40
     */
    cxxopts::Options options("Consolidate Unary");
    cxxopts::ParseResult options_vars;

    options.add_options("Program Options")
        ("help", "Display help information")
        ("prove", "Create a proof");

    options_vars = options.parse(argc, argv);

    try {
        options.add_options("Program Options")
            ("help", "Display help information")
            ("prove", "Create a proof");

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << "Usage: " << argv[0] << " [options] [size]" << endl;
        cout << endl;
        cout << options.help() << endl;
        return EXIT_SUCCESS;
    }

    Problem p;

    // The Smart Table trees as output by random_smart_table.cc with seed 792395939
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
        options_vars.contains("prove") ? make_optional<ProofOptions>("consolidate_unary") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
