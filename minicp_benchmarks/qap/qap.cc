#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/constraints/not_equals.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <array>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>

#include <boost/program_options.hpp>

using namespace gcs;

using std::array;
using std::cerr;
using std::cout;
using std::endl;
using std::ifstream;
using std::make_optional;
using std::nullopt;
using std::to_string;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    namespace po = boost::program_options;

    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");

    po::options_description all_options{"All options"};
    all_options.add_options() //
        ("size", po::value<int>()->default_value(12), "Size of the problem to solve (max 12)");

    all_options.add(display_options);

    po::positional_options_description positional_options;
    positional_options
        .add("size", -1);

    po::variables_map options_vars;

    try {
        po::store(po::command_line_parser(argc, argv)
                      .options(all_options)
                      .positional(positional_options)
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

    cout << "Replicating the MiniCP Quadratic Assignment Problem benchmark." << endl;
    cout << "See Laurent D. Michel, Pierre Schaus, Pascal Van Hentenryck:" << endl;
    cout << "\"MiniCP: a lightweight solver for constraint programming.\"" << endl;
    cout << "Math. Program. Comput. 13(1): 133-184 (2021)." << endl;
    cout << endl;

    Problem p;

    constexpr int max_size = 12;
    int size = options_vars["size"].as<int>();
    if (size > max_size) {
        cerr << "Maximum size is " << max_size << endl;
        return EXIT_FAILURE;
    }

    array<array<int, max_size>, max_size> weight_consts{
        array<int, max_size>{0, 90, 10, 23, 43, 0, 0, 0, 0, 0, 0, 0},
        array<int, max_size>{90, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0},
        array<int, max_size>{10, 0, 0, 0, 0, 0, 26, 16, 0, 0, 0, 0},
        array<int, max_size>{23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
        array<int, max_size>{43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
        array<int, max_size>{0, 88, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0},
        array<int, max_size>{0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0},
        array<int, max_size>{0, 0, 16, 0, 0, 0, 0, 0, 0, 96, 0, 0},
        array<int, max_size>{0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 29, 0},
        array<int, max_size>{0, 0, 0, 0, 0, 0, 0, 96, 0, 0, 0, 37},
        array<int, max_size>{0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0},
        array<int, max_size>{0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0}};

    array<array<int, max_size>, max_size> distances_consts{
        array<int, max_size>{0, 36, 54, 26, 59, 72, 9, 34, 79, 17, 46, 95},
        array<int, max_size>{36, 0, 73, 35, 90, 58, 30, 78, 35, 44, 79, 36},
        array<int, max_size>{54, 73, 0, 21, 10, 97, 58, 66, 69, 61, 54, 63},
        array<int, max_size>{26, 35, 21, 0, 93, 12, 46, 40, 37, 48, 68, 85},
        array<int, max_size>{59, 90, 10, 93, 0, 64, 5, 29, 76, 16, 5, 76},
        array<int, max_size>{72, 58, 97, 12, 64, 0, 96, 55, 38, 54, 0, 34},
        array<int, max_size>{9, 30, 58, 46, 5, 96, 0, 83, 35, 11, 56, 37},
        array<int, max_size>{34, 78, 66, 40, 29, 55, 83, 0, 44, 12, 15, 80},
        array<int, max_size>{79, 35, 69, 37, 76, 38, 35, 44, 0, 64, 39, 33},
        array<int, max_size>{17, 44, 61, 48, 16, 54, 11, 12, 64, 0, 70, 86},
        array<int, max_size>{46, 79, 54, 68, 5, 0, 56, 15, 39, 70, 0, 18},
        array<int, max_size>{95, 36, 63, 85, 76, 34, 37, 80, 33, 86, 18, 0}};

    vector<vector<Integer>> distances_consts_integers;
    for (int d1 = 0; d1 < size; ++d1) {
        distances_consts_integers.emplace_back();
        for (int d2 = 0; d2 < size; ++d2)
            distances_consts_integers.back().push_back(Integer{distances_consts[d1][d2]});
    }

    auto max_distance = 0;
    for (int d1 = 0; d1 < size; ++d1)
        for (int d2 = 0; d2 < size; ++d2)
            if (distances_consts[d1][d2] > max_distance)
                max_distance = distances_consts[d1][d2];

    auto max_weight = 0;
    for (int d1 = 0; d1 < size; ++d1)
        for (int d2 = 0; d2 < size; ++d2)
            if (weight_consts[d1][d2] > max_weight)
                max_weight = weight_consts[d1][d2];

    auto xs = p.create_integer_variable_vector(size, 0_i, Integer{size - 1}, "xs");

    // p.post(AllDifferent{ xs });
    for (int i = 0; i < size; ++i)
        for (int j = i + 1; j < size; ++j)
            p.post(NotEquals{xs[i], xs[j]});

    WeightedSum wcosts;
    for (int i = 0; i < size; ++i) {
        for (int j = 0; j < size; ++j) {
            auto d_xsi_xsj = p.create_integer_variable(0_i, Integer{max_distance} + 1_i,
                "dxs" + to_string(i) + "xs" + to_string(j));
            p.post(Element2DConstantArray{d_xsi_xsj, xs[i], xs[j], &distances_consts_integers});
            wcosts += Integer{weight_consts[i][j]} * d_xsi_xsj;
        }
    }

    auto cost = p.create_integer_variable(0_i, 100000_i, "cost");
    p.post(move(wcosts) == 1_i * cost);
    p.minimise(cost);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "cost: " << s(cost) << endl;
                return true;
            },
            .branch = branch_on_dom(xs),
            .guess = [&](const CurrentState & state, IntegerVariableID var) -> vector<IntegerVariableCondition> {
                return vector<IntegerVariableCondition>{var == state.lower_bound(var), var != state.lower_bound(var)};
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>("qap.opb", "qap.pbp") : nullopt);

    cout << stats << endl;

    return EXIT_SUCCESS;
}
