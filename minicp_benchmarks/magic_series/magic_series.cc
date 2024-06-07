#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <util/enumerate.hh>

#include <boost/program_options.hpp>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <vector>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::vector;

namespace po = boost::program_options;

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof")          //
        ("extra-constraints", "Use extra constraints described in the MiniCP paper");

    po::options_description all_options{"All options"};
    all_options.add_options() //
        ("size", po::value<int>()->default_value(300), "Size of the problem to solve");

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

    cout << "Replicating the MiniCP Magic Series benchmark." << endl;
    cout << "See Laurent D. Michel, Pierre Schaus, Pascal Van Hentenryck:" << endl;
    cout << "\"MiniCP: a lightweight solver for constraint programming.\"" << endl;
    cout << "Math. Program. Comput. 13(1): 133-184 (2021)." << endl;
    cout << "This should take 1193 recursions with default options." << endl;
    cout << endl;

    int size = options_vars["size"].as<int>();
    Problem p;

    auto series = p.create_integer_variable_vector(size, 0_i, Integer{size - 1}, "series");

    for (int i = 0; i < size; ++i) {
        WeightedSum coeff_vars;
        for (int j = 0; j < size; ++j) {
            auto series_j_eq_i = p.create_integer_variable(0_i, 1_i);
            p.post(EqualsIff{series[j], constant_variable(Integer{i}), series_j_eq_i == 1_i});
            coeff_vars += 1_i * series_j_eq_i;
        }

        p.post(move(coeff_vars) == 1_i * series[i]);
    }

    WeightedSum sum_s;
    for (auto & s : series)
        sum_s += 1_i * s;
    p.post(move(sum_s) == Integer{size});

    // Although this is discussed in the text, it isn't included in the executed
    // benchmarks.
    if (options_vars.contains("extra-constraints")) {
        WeightedSum sum_mul_s;
        for (const auto & [idx, s] : enumerate(series))
            sum_mul_s += Integer(idx) * s;
        p.post(move(sum_mul_s) == Integer{size});
    }

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "solution:";
                for (auto & v : series)
                    cout << " " << s(v);
                cout << endl;

                return true;
            },
            .branch = branch_with(variable_order::dom(series), value_order::smallest_in())},
        options_vars.contains("prove") ? make_optional<ProofOptions>("magic_series.opb", "magic_series.pbp") : nullopt);

    cout << stats;

    return EXIT_SUCCESS;
}
