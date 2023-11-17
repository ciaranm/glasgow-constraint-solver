#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <random>
#include <string>

#include <boost/program_options.hpp>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/in.hh>

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

namespace po = boost::program_options;

auto create_graph_from_seed(int n, double p, unsigned int seed) -> pair<vector<vector<long>>, unsigned int>
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

    return make_pair(distances, seed);
}

auto generate_random_graph(int n, double p) -> pair<vector<vector<long>>, unsigned int>
{
    std::random_device rd;
    auto seed = rd();
    return create_graph_from_seed(n, p, seed);
}

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof")          //

        po::options_description all_options{"All options"};

    all_options.add_options()(
        "n", po::value<int>()->default_value(3), "Integer value n.");
    ;
    all_options.add_options()(
        "seed", po::value<int>(), "Random seed.");

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

    if (options_vars.contains("seed")) {
    }
    else {
        int smallest_n = 3;
        int largest_n = 15;
        int repetitions = 5;

        for (int n = smallest_n; n <= largest_n; ++n) {
            for (int r = 0; r < repetitions; ++r) {
                Problem p;
                auto [distances, seed] = generate_random_graph(n, 0.3);
                auto x = p.create_integer_variable_vector(n, 0_i, Integer{n - 1});
                cout << "Seed: " << seed << endl;
                //            for (int i = 0; i < n; ++i) {
                //                for (int j = 0; cmp_less(j, distances[i].size()); ++j) {
                //                    cout << distances[i][j] << " ";
                //                }
                //                cout << endl;
                //            }

                for (int loc1 = 0; loc1 < n; loc1++) {
                    for (int loc2 = 0; loc2 < n; loc2++) {
                        if (distances[loc1][loc2] < 0) {
                            p.post(NotEquals{x[loc1], ConstantIntegerVariableID{Integer{loc2}}});
                        }
                    }
                }

                p.post(Circuit{x});

                // Minimise the distance between any two stops
                auto max_leg = p.create_integer_variable(0_i, 100_i, "max_leg");
                for (int loc1 = 0; loc1 < n; loc1++) {
                    for (int loc2 = 0; loc2 < n; loc2++) {
                        p.post(LessThanIf{ConstantIntegerVariableID{Integer{distances[loc1][loc2]}}, max_leg,
                            x[loc1] == Integer{loc2}});
                    }
                }

                p.minimise(max_leg);

                cout << "n = " << n << endl;
                auto stats = solve_with(p,
                    SolveCallbacks{
                        .solution = [&](const CurrentState & s) -> bool {
                            //                        for (const auto & v : x) {
                            //                            cout << s(v) << " ";
                            //                        }
                            //                        cout << endl;
                            //                        cout << 0 << " -> " << s(x[0]);
                            //                        auto current = s(x[0]);
                            //                        while (current != 0_i) {
                            //                            cout << " -> ";
                            //                            cout << s(x[current.raw_value]);
                            //                            current = s(x[current.raw_value]);
                            //                        }
                            //                        cout << "\n\n";
                            //                        return true;
                            return true;
                        },
                    },
                    make_optional<ProofOptions>("circuit_random.opb", "circuit_random.veripb"));
                if (! system("veripb circuit_random.opb circuit_random.veripb > trace.opb"))
                    return EXIT_FAILURE;

                cout << "Num solutions: " << stats.solutions << endl;
                //        cout << stats;
                //            cout << "------";
            }
        }
    }

    return EXIT_SUCCESS;
}
