#include <cxxopts.hpp>

#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/not_equals.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <random>

using namespace gcs;

using std::cerr;
using std::cmp_less;
using std::cout;
using std::endl;
using std::make_optional;
using std::make_pair;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::string;
using std::uniform_real_distribution;
using std::vector;

static const double EDGE_PROBABILITY = 0.7;

auto create_graph_from_seed(int n, double p, unsigned int seed) -> vector<vector<long>>
{
    std::mt19937 gen(seed);
    std::uniform_real_distribution<> dis(0.0, 1.0);

    std::vector<std::vector<long>> distances(n);

    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {

            if (dis(gen) < p && i != j) {
                distances[i].push_back(int(dis(gen) * 100)); // Edge from i to j
            }
            else {
                distances[i].push_back(-1);
            }
        }
    }

    return distances;
}

Stats run_circuit_problem(int n, const vector<vector<long>> & distances, SCCOptions options, bool print_solutions, bool prove, string proof_prefix)
{
    Problem p;
    auto x = p.create_integer_variable_vector(n, 0_i, Integer{n - 1});

    for (int loc1 = 0; loc1 < n; loc1++) {
        for (int loc2 = 0; loc2 < n; loc2++) {
            if (distances[loc1][loc2] < 0) {
                p.post(NotEquals{x[loc1], ConstantIntegerVariableID{Integer{loc2}}});
            }
        }
    }
    auto use_gac_all_different = false;
    p.post(Circuit{x, use_gac_all_different, options});

    // Minimise the distance between any two stops
    auto max_leg = p.create_integer_variable(0_i, 100_i, "max_leg");
    for (int loc1 = 0; loc1 < n; loc1++) {
        for (int loc2 = 0; loc2 < n; loc2++) {
            p.post(LessThanIf{ConstantIntegerVariableID{Integer{distances[loc1][loc2]}}, max_leg,
                x[loc1] == Integer{loc2}});
        }
    }

    p.minimise(max_leg);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                if (print_solutions) {
                    for (const auto & v : x) {
                        cout << s(v) << " ";
                    }
                    cout << endl;
                    cout << 0 << " -> " << s(x[0]);
                    auto current = s(x[0]);
                    while (current != 0_i) {
                        cout << " -> ";
                        cout << s(x[current.raw_value]);
                        current = s(x[current.raw_value]);
                    }
                    cout << "\nMax leg = " << s(max_leg) << endl;
                    cout << "\n";
                }
                return true;
            },
        },
        prove ? make_optional<ProofOptions>(proof_prefix) : nullopt);
    return stats;
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options command_options("Program options");
    cxxopts::ParseResult options_vars;

    try {
        command_options.add_options("Program options") //
            ("help", "Display help information")       //
            ("prove", "Create a proof");

        command_options.add_options()                                            //
            ("n", "Integer value n.", cxxopts::value<int>()->default_value("3")) //
            ("seed", "Random seed.", cxxopts::value<int>()->default_value("-1")) //
            ("stats", "Print statistics")                                        //
            ("proof-prefix", "Path and name of the opb and pbp files",           //
                cxxopts::value<string>()->default_value("circuit_random"))       //
            ("print-distances", "Print the input graph used for the probllem")   //
            ("print-solutions", "Print each solution found while optimising")    //
            ("no-prune-root", "SCC inference")                                   //
            ("no-prune-skip", "SCC inference")                                   //
            ("no-fix-req", "SCC inference")                                      //
            ("no-prune-within", "SCC inference")                                 //
            ("no-prove-am1-contradiction", "SCC optimisation")                   //
            ("prove-using-dominance", "SCC inference")                           //
            ("enable-comments", "SCC inference");

        options_vars = command_options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        cerr << "Error: " << e.what() << endl;
        cerr << "Try " << argv[0] << " --help" << endl;
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        cout << "Usage: " << argv[0] << " [options] [size]" << endl;
        cout << endl;
        cout << command_options.help() << endl;
        return EXIT_SUCCESS;
    }

    SCCOptions options{
        ! options_vars.contains("no-prune-root"),
        ! options_vars.contains("no-prune-skip"),
        ! options_vars.contains("no-fix-req"),
        ! options_vars.contains("no-prune-within"),
        false,
        options_vars.contains("enable_comments"),
        ! options_vars.contains("no-prove-am1-contradiction"),
    };

    auto n = options_vars["n"].as<int>();
    auto seed = options_vars["seed"].as<int>();
    auto proof_prefix = options_vars["proof-prefix"].as<string>();
    auto print_distances = options_vars.contains("print-distances");
    auto print_solutions = options_vars.contains("print-solutions");
    auto print_stats = options_vars.contains("stats");
    auto prove = options_vars.contains("prove");

    if (seed == -1) {
        random_device rand_dev;
        seed = rand_dev();
    }

    auto distances = create_graph_from_seed(n, EDGE_PROBABILITY, seed);
    if (print_distances) {
        for (unsigned int i = 0; i < distances.size(); ++i) {
            cout << i << ": ";
            for (unsigned int j = 0; j < distances[i].size(); ++j) {
                if (distances[i][j] != -1)
                    cout << j << " ";
            }
            cout << endl;
        }
    }

    auto stats = run_circuit_problem(n, distances, options, print_solutions, prove, proof_prefix);

    if (print_stats) {
        cout << "seed: " << seed << endl;
        cout << stats << endl;
    }

    return EXIT_SUCCESS;
}
