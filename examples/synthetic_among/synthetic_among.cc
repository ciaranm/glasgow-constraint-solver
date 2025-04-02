#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <iostream>
#include <string>

#include <boost/program_options.hpp>
#include <gcs/constraints/among.hh>
#include <gcs/innards/proofs/lp_justifier.hh>
#include <random>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::max;
using std::min;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::string;
using std::to_string;
using std::uniform_int_distribution;
using std::vector;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");         //

    po::options_description all_options{"All options"};

    all_options.add_options()(
        "n", po::value<int>()->default_value(80), "Integer value n.")           //
        ("seed", po::value<int>()->default_value(0), "Seed for randomisation.") //
        ("lp", "Use LP justifications")                                         //
        ;

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

    auto n = options_vars["n"].as<int>();
    auto seed = options_vars["seed"].as<int>();

    std::mt19937 rng(seed);
    optional<LPJustificationOptions> USE_LP_JUST = nullopt;
    if (options_vars.contains("lp")) {
        USE_LP_JUST = make_optional(LPJustificationOptions{});
    }

    Problem p;
    vector<vector<IntegerVariableID>> grid;
    grid.reserve(n);
    for (auto row = 0; row < n; row++) {
        grid.emplace_back(p.create_integer_variable_vector(n, 1_i, Integer{n}, "g"));
    }

    uniform_int_distribution<> rand1_to_n(1, n);

    // Create a grid of overlapping Among constraints
    for (auto row = 0; row < n; row++) {
        vector<Integer> voi;
        // Pick 4 random values
        while (voi.size() < 5) {
            auto randomValue = Integer{rand1_to_n(rng)};
            if (std::find(voi.begin(), voi.end(), randomValue) == voi.end()) {
                voi.push_back(randomValue);
            }
        }
        auto bnd1 = Integer{rand1_to_n(rng)};
        auto bnd2 = Integer{rand1_to_n(rng)};

        auto count = p.create_integer_variable(3_i, 8_i, "cr" + to_string(row));
        p.post(Among{grid[row], voi, count, USE_LP_JUST});
    }

    for (auto col = 0; col < n; col++) {
        vector<Integer> voi;
        // Pick 4 random values
        while (voi.size() < 5) {
            auto randomValue = Integer{rand1_to_n(rng)};
            if (std::find(voi.begin(), voi.end(), randomValue) == voi.end()) {
                voi.push_back(randomValue);
            }
        }

        vector<IntegerVariableID> column;
        column.reserve(n);
        for (auto row = 0; row < n; row++) {
            column.emplace_back(grid[row][col]);
        }
        auto bnd1 = Integer{rand1_to_n(rng)};

        auto count = p.create_integer_variable(4_i, 8_i, "cc" + to_string(col));
        p.post(Among{column, voi, count, USE_LP_JUST});
    }

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "Found a solution." << endl;
                return false;
            },
        },
        options_vars.contains("prove") ? make_optional<ProofOptions>("synthetic_among") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
