#include <cxxopts.hpp>
#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/in.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

auto post_constraints(Problem & p, vector<IntegerVariableID> & nodes)
{
    /**
     * Domains set as in Figure 4. fro K. G. Francis and P. J. Stuckey,
     * ‘Explaining circuit propagation’, Constraints, vol. 19, no. 1, pp. 1–29, Jan. 2014,
     * doi: 10.1007/s10601-013-9148-0.
     *
     * There is only one SCC, but multiple subtrees explored below the root in the DFS.
     **/

    p.post(In{nodes[0], {1_i, 4_i, 5_i}});
    p.post(In{nodes[1], {2_i, 3_i}});
    p.post(In{nodes[2], {0_i}});
    p.post(In{nodes[3], {2_i}});
    p.post(In{nodes[4], {1_i, 3_i}});
    p.post(In{nodes[5], {0_i, 6_i}});
    p.post(In{nodes[6], {3_i, 4_i}});
}
auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Program options");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program options")("help", "Display help information")("prove", "Create a proof");

        options.add_options("All options")("propagator", "Specify which circuit propagation algorithm to use (prevent/scc)",
            cxxopts::value<string>()->default_value("scc"));

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

    if (options_vars.contains("propagator")) {
        const string propagator_value = options_vars["propagator"].as<string>();
        if (propagator_value != "prevent" && propagator_value != "scc") {
            cerr << "Error: Invalid value for propagator. Use 'scc' or 'prevent'." << endl;
            return EXIT_FAILURE;
        }
    }

    Problem p;
    auto nodes = p.create_integer_variable_vector(7, 0_i, 6_i);

    post_constraints(p, nodes);

    if (options_vars["propagator"].as<string>() == "prevent") {
        p.post(CircuitPrevent{nodes});
    }
    else if (options_vars["propagator"].as<string>() == "scc") {
        p.post(CircuitSCC{nodes});
    }
    else {
        p.post(Circuit{nodes});
    }

    auto stats = solve_with(
        p,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
            for (const auto & v : nodes) {
                cout << s(v) << " ";
            }
            cout << endl;
            cout << 0 << " -> " << s(nodes[0]);
            auto current = s(nodes[0]);
            while (current != 0_i) {
                cout << " -> ";
                cout << s(nodes[current.raw_value]);
                current = s(nodes[current.raw_value]);
            }
            cout << "\n\n";
            return true;
        }},
        options_vars.contains("prove") ? make_optional<ProofOptions>("circuit_small") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
