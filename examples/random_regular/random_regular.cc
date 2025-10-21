#include <gcs/constraints/comparison.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cxxopts.hpp>

#include <gcs/constraints/regular.hh>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::iota;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::shuffle;
using std::ssize;
using std::string;
using std::stringstream;
using std::uniform_int_distribution;
using std::vector;

using namespace innards;

auto index_of(const IntegerVariableID & val, const vector<IntegerVariableID> & vec) -> int
{
    ptrdiff_t pos = distance(vec.begin(), find(vec.begin(), vec.end(), val));
    return (int)pos;
}

auto test_regular(const int & n, mt19937 & rng, bool prove)
{
    stringstream string_rep;

    Problem p;

    auto x = p.create_integer_variable_vector(n, 0_i, Integer{n - 1}, "x");
    uniform_int_distribution<> dist_2_to_4n(2, 4 * n);
    uniform_int_distribution<> dist_m1_to_nm1(-1, n - 1);
    auto num_states = dist_2_to_4n(rng);
    uniform_int_distribution<> dist_1_to_num_states(1, num_states - 1);
    uniform_int_distribution<> dist_m1_to_num_states(-1, num_states - 1);

    string_rep << "#states\n";
    for (int i = 0; i < num_states; i++) {
        string_rep << "s" << i << "\n";
    }
    string_rep << "#initial\ns0\n";

    auto num_final_states = dist_1_to_num_states(rng);

    vector<long> states(num_states);
    iota(states.begin(), states.end(), 0);
    shuffle(states.begin(), states.end(), rng);
    vector<long> final_states(states.begin(), states.begin() + num_final_states);

    string_rep << "#accepting\n";
    for (const auto & i : final_states) {
        string_rep << "s" << i << "\n";
    }
    string_rep << "#alphabet\n";
    vector<Integer> symbols{};
    for (int i = 0; i < n; i++) {
        symbols.emplace_back(i);
        string_rep << i << "\n";
    }

    string_rep << "#transitions\n";
    vector<vector<long>> transitions(num_states, vector<long>(n));
    for (int i = 0; i < num_states; i++) {
        for (int j = 0; j < n; j++) {
            transitions[i][j] = dist_m1_to_num_states(rng);
            if (transitions[i][j] != -1)
                string_rep << "s" << i << ":" << j << ">s" << transitions[i][j] << "\n";
        }
    }

    p.post(Regular{x, symbols, num_states, transitions, final_states});

    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool {
                return true;
            }},
        prove ? make_optional(ProofOptions{"random_regular"}) : nullopt);

    //        cout << "Num solutions: " << stats.solutions << endl;

    return true;
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Random Regular Language Membership Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                                                         //
            ("help", "Display help information")                                                                       //
            ("prove", "Create a proof")                                                                                //
            ("seed", "Seed for random DFA generator (-1 for random seed)", cxxopts::value<int>()->default_value("-1")) //
            ("n", "Max sequence length", cxxopts::value<int>()->default_value("6"));

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

    auto seed = options_vars["seed"].as<int>();
    auto max_n = options_vars["n"].as<int>();

    if (seed == -1) {
        random_device rand_dev;
        seed = rand_dev();
    }
    std::mt19937 rng(seed);
    // cout << "Seed for random DFAs for Regular: " << seed << endl;
    //    mt19937 rng(0); // Switch to this to have it the same every time.
    for (int n = 3; n < max_n; n++) {
        for (int r = 0; r < 10 / n; r++) {
            if (! test_regular(n, rng, options_vars.contains("prove"))) {
                cout << "n == " << n << " r == " << r << endl;
                return EXIT_FAILURE;
            }
        }
    }

    return EXIT_SUCCESS;
}
