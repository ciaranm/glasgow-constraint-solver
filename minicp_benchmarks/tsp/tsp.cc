#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <vector>

#include <boost/program_options.hpp>

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
        ("prove", "Create a proof");

    po::options_description all_options{"All options"};

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
        cout << "Usage: " << argv[0] << " [options]" << endl;
        cout << endl;
        cout << display_options << endl;
        return EXIT_SUCCESS;
    }

    cout << "Replicating the TSP benchmark." << endl;
    cout << "See Laurent D. Michel, Pierre Schaus, Pascal Van Hentenryck:" << endl;
    cout << "\"MiniCP: a lightweight solver for constraint programming.\"" << endl;
    cout << "Math. Program. Comput. 13(1): 133-184 (2021)." << endl;
    cout << endl;

    // instance gr17 https://people.sc.fsu.edu/~jburkardt/datasets/tsp/gr17_d.txt
    vector<vector<Integer>> distances{
        {0_i, 633_i, 257_i, 91_i, 412_i, 150_i, 80_i, 134_i, 259_i, 505_i, 353_i, 324_i, 70_i, 211_i, 268_i, 246_i, 121_i},
        {633_i, 0_i, 390_i, 661_i, 227_i, 488_i, 572_i, 530_i, 555_i, 289_i, 282_i, 638_i, 567_i, 466_i, 420_i, 745_i, 518_i},
        {257_i, 390_i, 0_i, 228_i, 169_i, 112_i, 196_i, 154_i, 372_i, 262_i, 110_i, 437_i, 191_i, 74_i, 53_i, 472_i, 142_i},
        {91_i, 661_i, 228_i, 0_i, 383_i, 120_i, 77_i, 105_i, 175_i, 476_i, 324_i, 240_i, 27_i, 182_i, 239_i, 237_i, 84_i},
        {412_i, 227_i, 169_i, 383_i, 0_i, 267_i, 351_i, 309_i, 338_i, 196_i, 61_i, 421_i, 346_i, 243_i, 199_i, 528_i, 297_i},
        {150_i, 488_i, 112_i, 120_i, 267_i, 0_i, 63_i, 34_i, 264_i, 360_i, 208_i, 329_i, 83_i, 105_i, 123_i, 364_i, 35_i},
        {80_i, 572_i, 196_i, 77_i, 351_i, 63_i, 0_i, 29_i, 232_i, 444_i, 292_i, 297_i, 47_i, 150_i, 207_i, 332_i, 29_i},
        {134_i, 530_i, 154_i, 105_i, 309_i, 34_i, 29_i, 0_i, 249_i, 402_i, 250_i, 314_i, 68_i, 108_i, 165_i, 349_i, 36_i},
        {259_i, 555_i, 372_i, 175_i, 338_i, 264_i, 232_i, 249_i, 0_i, 495_i, 352_i, 95_i, 189_i, 326_i, 383_i, 202_i, 236_i},
        {505_i, 289_i, 262_i, 476_i, 196_i, 360_i, 444_i, 402_i, 495_i, 0_i, 154_i, 578_i, 439_i, 336_i, 240_i, 685_i, 390_i},
        {353_i, 282_i, 110_i, 324_i, 61_i, 208_i, 292_i, 250_i, 352_i, 154_i, 0_i, 435_i, 287_i, 184_i, 140_i, 542_i, 238_i},
        {324_i, 638_i, 437_i, 240_i, 421_i, 329_i, 297_i, 314_i, 95_i, 578_i, 435_i, 0_i, 254_i, 391_i, 448_i, 157_i, 301_i},
        {70_i, 567_i, 191_i, 27_i, 346_i, 83_i, 47_i, 68_i, 189_i, 439_i, 287_i, 254_i, 0_i, 145_i, 202_i, 289_i, 55_i},
        {211_i, 466_i, 74_i, 182_i, 243_i, 105_i, 150_i, 108_i, 326_i, 336_i, 184_i, 391_i, 145_i, 0_i, 57_i, 426_i, 96_i},
        {268_i, 420_i, 53_i, 239_i, 199_i, 123_i, 207_i, 165_i, 383_i, 240_i, 140_i, 448_i, 202_i, 57_i, 0_i, 483_i, 153_i},
        {246_i, 745_i, 472_i, 237_i, 528_i, 364_i, 332_i, 349_i, 202_i, 685_i, 542_i, 157_i, 289_i, 426_i, 483_i, 0_i, 336_i},
        {121_i, 518_i, 142_i, 84_i, 297_i, 35_i, 29_i, 36_i, 236_i, 390_i, 238_i, 301_i, 55_i, 96_i, 153_i, 336_i, 0_i}};

    Problem p;

    auto n = distances.size();
    auto succ = p.create_integer_variable_vector(n, 0_i, Integer(n - 1));
    auto dist = p.create_integer_variable_vector(n, 0_i, 745_i);

    p.post(Circuit{succ, false});
    for (unsigned i = 0; i < n; ++i)
        p.post(ElementConstantArray{dist[i], succ[i], &distances[i]});

    auto obj = p.create_integer_variable(0_i, 1000000_i, "obj");
    WeightedSum dist_sum;
    for (auto & s : dist)
        dist_sum += 1_i * s;
    p.post(dist_sum == 1_i * obj);
    p.minimise(obj);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "distance: " << s(obj) << endl;
                return true;
            },
            .branch = branch_on_dom(succ),
            .guess = [&](const CurrentState & state, IntegerVariableID var) -> vector<IntegerVariableCondition> {
                return vector<IntegerVariableCondition>{var == state.lower_bound(var), var != state.lower_bound(var)};
            }},
        options_vars.contains("prove") ? make_optional<ProofOptions>("tsp.opb", "tsp.pbp") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
