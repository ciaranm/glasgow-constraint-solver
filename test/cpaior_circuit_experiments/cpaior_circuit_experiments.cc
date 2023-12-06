#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <array>
#include <boost/program_options.hpp>
#include <cstdio>
#include <fstream>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/in.hh>
#include <iostream>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>

using namespace gcs;
using std::cerr;
using std::cmp_less;
using std::cout;
using std::endl;
using std::make_optional;
using std::make_pair;
using std::make_tuple;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::string;
using std::to_string;
using std::tuple;
using std::uniform_real_distribution;
using std::vector;
using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;
namespace po = boost::program_options;

// https://stackoverflow.com/questions/478898/how-do-i-execute-a-command-and-get-the-output-of-the-command-within-c-using-po
std::string run_and_get_result(string cmd)
{
    auto cmd_str = cmd.c_str();
    std::array<char, 128> buffer;
    std::string result;
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd_str, "r"), pclose);
    if (! pipe) {
        throw std::runtime_error("popen() failed!");
    }
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        result += buffer.data();
    }
    if (result.back() == '\n')
        result.pop_back();

    return result;
}

auto generate_random_graph(int n, double p, mt19937 & gen) -> vector<vector<long>>
{
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

auto test_circuit_problem(int n, const vector<vector<long>> & distances, string name, long i, long j, int verify_up_to) -> tuple<microseconds, microseconds, microseconds, Stats>
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

    p.post(Circuit{x, false});

    // Minimise the distance between any two stops
    auto max_leg = p.create_integer_variable(0_i, 100_i, "max_leg");
    for (int loc1 = 0; loc1 < n; loc1++) {
        for (int loc2 = 0; loc2 < n; loc2++) {
            p.post(LessThanIf{ConstantIntegerVariableID{Integer{distances[loc1][loc2]}}, max_leg,
                x[loc1] == Integer{loc2}});
        }
    }

    p.minimise(max_leg);

    auto proof = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                return true;
            },
        },
        make_optional<ProofOptions>(name + ".opb", name + ".veripb"));

    auto verification_time = microseconds{0};
    if (i < verify_up_to) {
        auto verify_start_time = steady_clock::now();
        const auto command = "veripb " + name + ".opb " + name + ".veripb";
        if (0 != system(command.c_str())) {
            cout << proof;
            cout << "n: " << n << endl;
            throw new UnexpectedException{"Verification failed!"};
        }
        verification_time = duration_cast<microseconds>(steady_clock::now() - verify_start_time);
    }
    // system("python3 check_inferences.py");

    auto no_proof = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                return true;
            },
        },
        nullopt);

    return make_tuple(no_proof.solve_time, proof.solve_time, verification_time, no_proof);
}

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options() //
        ("help", "Display help information");

    po::options_description all_options{"All options"};

    all_options.add_options()(
        "min_n", po::value<int>()->default_value(3), "Smallest number of vertices.");

    all_options.add_options()(
        "max_n", po::value<int>()->default_value(10), "Largest number of vertices.");

    all_options.add_options()(
        "seed", po::value<unsigned int>(), "Random seed");

    all_options.add_options()(
        "edge_p", po::value<double>()->default_value(0.5), "Edge probability for random graphs");

    all_options.add_options()(
        "repetitions", po::value<int>()->default_value(5), "Number of repeats for each vertex count.");

    all_options.add_options()(
        "verify_up_to", po::value<int>()->default_value(30), "Largest n we want to verify on the spot for");

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
    unsigned int seed;

    if (! options_vars.contains("seed")) {
        std::random_device rd;
        seed = rd();
    }
    else {
        seed = options_vars["seed"].as<unsigned int>();
    }

    auto edge_probability = options_vars["edge_p"].as<double>();
    auto repetitions = options_vars["repetitions"].as<int>();
    std::mt19937 gen(seed);

    std::ofstream outputFile("circuit_experiment_output.csv");

    if (outputFile.is_open()) {
        outputFile << "n, NoProofTime, ProofTime, VerificationTime, SlowDown, Recursions, Failures, Propagations, "
                   << "EffectualPropagations, ContradictingPropagations, Solutions, MaxDepth, NPropagators, DisconnectedCount, "
                   << "PruneRootCount, PruneToRootCount, FixReqCount, NoBackedgesCount, MultipleSCCCount, PruneSkipCount\n";
        outputFile.close();
    }
    else {
        std::cerr << "Unable to open the file." << std::endl;
    }

    for (auto i = options_vars["min_n"].as<int>(); i <= options_vars["max_n"].as<int>(); i++) {
        for (auto j = 0; j < repetitions; j++) {
            std::ofstream outputFileApp("circuit_experiment_output.csv", std::ios::app);
            if (outputFileApp.is_open()) {
                auto distances = generate_random_graph(i, edge_probability, gen);
                cout << "n = " << i << " instance = " << j << endl;
                auto name = "circui_experiment_" + to_string(i) + "_" + to_string(j);
                auto [no_proof_time, proof_time, verification_time, stats] = test_circuit_problem(i, distances, name, i, j, options_vars["verify_up_to"].as<int>());
                auto slowdown = 1.0 * proof_time.count() / no_proof_time.count();
                outputFileApp << i << ", "
                              << no_proof_time.count() << ", "
                              << proof_time.count() << ", "
                              << verification_time.count() << ", "
                              << slowdown << ", "
                              << stats.recursions << ", " << stats.failures << ", "
                              << stats.propagations << ", "
                              << stats.effectful_propagations << ", "
                              << stats.contradicting_propagations << ", "
                              << stats.solutions << ", "
                              << stats.max_depth << ", "
                              << stats.n_propagators << ", "
                              << run_and_get_result("cat " + name + ".veripb | grep --count \"Disconnected graph\"") << ", "
                              << run_and_get_result("cat " + name + ".veripb | grep --count \"Prune impossible edges from root node\"") << ", "
                              << run_and_get_result("cat " + name + ".veripb | grep --count \"Pruning edge to the root\"") << ", "
                              << run_and_get_result("cat " + name + ".veripb | grep --count \"Fix required back edge\"") << ", "
                              << run_and_get_result("cat " + name + ".veripb | grep --count \"No back edges\"") << ", "
                              << run_and_get_result("cat " + name + ".veripb | grep --count \"More than one SCC\"") << ", "
                              << run_and_get_result("cat " + name + ".veripb | grep --count \"Pruning edge that would skip subtree\"") << "\n";
            }
            else {
                std::cerr << "Unable to open the file." << std::endl;
            }
            outputFileApp.close();
        }
    }
}
