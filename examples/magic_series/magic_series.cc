/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
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
    Problem p = options_vars.contains("prove") ? Problem{ProofOptions{"magic_series.opb", "magic_series.veripb"}} : Problem{};

    auto series = p.create_integer_variable_vector(size, 0_i, Integer{size - 1}, "series");

    for (int i = 0; i < size; ++i) {
        Linear coeff_vars;
        for (int j = 0; j < size; ++j) {
            auto series_j_eq_i = p.create_integer_variable(0_i, 1_i);
            p.post(EqualsIff{series[j], constant_variable(Integer{i}), series_j_eq_i == 1_i});
            coeff_vars.emplace_back(1_i, series_j_eq_i);
        }

        coeff_vars.emplace_back(-1_i, series[i]);
        p.post(LinearEquality{move(coeff_vars), 0_i});
    }

    Linear sum_s;
    for (auto & s : series)
        sum_s.emplace_back(1_i, s);
    p.post(LinearEquality{move(sum_s), Integer{size}});

    // Although this is discussed in the text, it isn't included in the executed
    // benchmarks.
    if (options_vars.contains("extra-constraints")) {
        Linear sum_mul_s;
        for (const auto & [idx, s] : enumerate(series))
            sum_mul_s.emplace_back(Integer(idx), s);
        p.post(LinearEquality{move(sum_mul_s), Integer{size}});
    }

    p.branch_on(series);

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "solution:";
                for (auto & v : series)
                    cout << " " << s(v);
                cout << endl;

                return true;
            },
            .guess = [&](const CurrentState & state, IntegerVariableID var) -> vector<Literal> {
                return vector<Literal>{var == state.lower_bound(var), var != state.lower_bound(var)};
            }});

    cout << stats;

    return EXIT_SUCCESS;
}
