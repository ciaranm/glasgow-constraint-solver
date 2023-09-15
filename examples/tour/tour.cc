#include <boost/program_options.hpp>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <vector>

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
    // Example for the circuit constraint: find a tour for some graph of locations
    // and minimise the distance between any two stops.

    // This is based on the circuit benchmark instances from
    // K. G. Francis and P. J. Stuckey, ‘Explaining circuit propagation’, Constraints, vol. 19, no. 1, pp. 1–29, Jan. 2014,
    // doi: 10.1007/s10601-013-9148-0.
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");         //

    po::options_description all_options{"All options"};
    all_options.add_options() //
        ("propagator", po::value<string>()->default_value("prevent_incremental"), "Specify which circuit propagation algorithm to use (prevent/prevent_incremental)");

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

    if (options_vars.contains("propagator")) {
        const string propagator_value = options_vars["propagator"].as<string>();
        if (propagator_value != "prevent" && propagator_value != "prevent_incremental") {
            cerr << "Error: Invalid value for propagator. Use 'prevent' or 'prevent_incremental'." << endl;
            return EXIT_FAILURE;
        }
    }

    int n = 20;
    Problem p;

    // Travel times between locations
    // -1 means no direct connection exists (no edge in the graph)
    vector<vector<int>> distance =
        {{0, -1, -1, -1, 83, 71, 22, -1, -1, -1, 69, -1, 76, 35, 14, 2, -1, -1, -1, 19},
            {-1, 0, -1, 19, -1, -1, -1, -1, -1, 87, 99, -1, -1, -1, -1, 96, -1, -1, -1, -1},
            {-1, -1, 0, -1, -1, -1, -1, -1, 45, -1, -1, 14, 42, 46, -1, -1, -1, -1, 64, 65},
            {-1, 19, -1, 0, -1, -1, -1, 5, -1, -1, -1, -1, -1, -1, 92, -1, -1, -1, 47, -1},
            {83, -1, -1, -1, 0, -1, 51, -1, -1, -1, -1, 20, -1, 17, 57, 48, 6, -1, 24, 84},
            {71, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1, -1, 25, -1, -1, -1, -1, -1, 18},
            {22, -1, -1, -1, 51, -1, 0, -1, 59, -1, -1, 94, -1, 99, -1, -1, -1, -1, -1, -1},
            {-1, -1, -1, 5, -1, -1, -1, 0, -1, -1, -1, 76, -1, -1, -1, 82, -1, -1, 76, 77},
            {-1, -1, 45, -1, -1, -1, 59, -1, 0, -1, -1, -1, 70, -1, 39, 20, -1, -1, -1, -1},
            {-1, 87, -1, -1, -1, -1, -1, -1, -1, 0, -1, 20, -1, -1, -1, -1, -1, 59, 54, 1},
            {69, 99, -1, -1, -1, -1, -1, -1, -1, -1, 0, -1, -1, 78, -1, -1, -1, -1, -1, -1},
            {-1, -1, 14, -1, 20, -1, 94, 76, -1, 20, -1, 0, -1, -1, 61, -1, -1, -1, -1, -1},
            {76, -1, 42, -1, -1, -1, -1, -1, 70, -1, -1, -1, 0, -1, -1, -1, 8, -1, 63, 74},
            {35, -1, 46, -1, 17, 25, 99, -1, -1, -1, 78, -1, -1, 0, -1, 56, -1, -1, 11, -1},
            {14, -1, -1, 92, 57, -1, -1, -1, 39, -1, -1, 61, -1, -1, 0, -1, -1, 21, -1, 16},
            {2, 96, -1, -1, 48, -1, -1, 82, 20, -1, -1, -1, -1, 56, -1, 0, -1, 99, -1, 14},
            {-1, -1, -1, -1, 6, -1, -1, -1, -1, -1, -1, -1, 8, -1, -1, -1, 0, -1, 67, 78},
            {-1, -1, -1, -1, -1, -1, -1, -1, -1, 59, -1, -1, -1, -1, 21, 99, -1, 0, -1, 73},
            {-1, -1, 64, 47, 24, -1, -1, 76, -1, 54, -1, -1, 63, 11, -1, -1, 67, -1, 0, -1},
            {19, -1, 65, -1, 84, 18, -1, 77, -1, 1, -1, -1, 74, -1, 16, 14, 78, 73, -1, 0}};

    // Successor variables
    vector<IntegerVariableID> succ = p.create_integer_variable_vector(n, 0_i, Integer{n - 1});

    // Only use allowed legs (remove non edges from domains)
    for (int loc1 = 0; loc1 < n; loc1++) {
        for (int loc2 = 0; loc2 < n; loc2++) {
            if (distance[loc1][loc2] < 0) {
                p.post(NotEquals{succ[loc1], ConstantIntegerVariableID{Integer{loc2}}});
            }
        }
    }

    if (options_vars["propagator"].as<string>() == "prevent") {
        p.post(CircuitPrevent{succ, false});
    }
    else if (options_vars["propagator"].as<string>() == "prevent_incremental") {
        p.post(CircuitPreventIncremental{succ, false});
    }
    else {
        p.post(Circuit{succ, false});
    }

    // Minimise the distance between any two stops
    auto max_leg = p.create_integer_variable(0_i, 100_i, "max_leg");
    for (int loc1 = 0; loc1 < n; loc1++) {
        for (int loc2 = 0; loc2 < n; loc2++) {
            p.post(LessThanIf{ConstantIntegerVariableID{Integer{distance[loc1][loc2]}}, max_leg,
                succ[loc1] == Integer{loc2}});
        }
    }

    p.minimise(max_leg);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                for (const auto & v : succ) {
                    cout << s(v) << " ";
                }
                cout << endl;
                cout << 0 << " -> " << s(succ[0]);
                auto current = s(succ[0]);
                while (current != 0_i) {
                    cout << " -> ";
                    cout << s(succ[current.raw_value]);
                    current = s(succ[current.raw_value]);
                }
                cout << "\n\n";
                return true;
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>("tour.opb", "tour.veripb") : nullopt);

    cout << stats;
    return EXIT_SUCCESS;
}
