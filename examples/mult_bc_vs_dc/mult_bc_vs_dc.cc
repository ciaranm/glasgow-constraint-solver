#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/mult_bc.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <boost/program_options.hpp>
#include <cstdlib>
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#include <gcs/presolvers/auto_table.hh>
#include <gcs/presolvers/proof_auto_table.hh>
#include <iostream>
#include <random>
#include <string>
#include <tuple>

using namespace gcs;
using namespace gcs::test_innards;

using std::cerr;
using std::cout;
using std::endl;
using std::flush;
using std::function;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
using std::set;
using std::string;
using std::tuple;
using std::uniform_int_distribution;
using std::vector;

using fmt::print;
using fmt::println;

namespace po = boost::program_options;
enum TestType
{
    NO_PROOFS,
    BC_PROOFS,
    DC_PROOFS
};

auto run_mult_test(pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range, TestType test_type) -> bool
{
    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
    auto stats = Stats{};
    switch (test_type) {
    case NO_PROOFS:
        p.post(MultBC{v1, v2, v3});
        stats = solve(p, [&](const CurrentState &) -> bool { return false; });
        cout << stats.solve_time.count() << ",";
        return true;
    case BC_PROOFS: {
        p.post(MultBC{v1, v2, v3});
        stats = solve(
            p, [&](const CurrentState &) -> bool { return false; }, make_optional(ProofOptions{"mult_experiment_bc.opb", "mult_experiment_bc.pbp"}));
        cout << stats.solve_time.count() << ",";

        auto start_time_bc = std::chrono::steady_clock::now();
        auto result_bc = system("veripb mult_experiment_bc.opb mult_experiment_bc.pbp >/dev/null");
        auto verify_time_bc = std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - start_time_bc).count();
        cout << verify_time_bc << ",";
        return result_bc == EXIT_SUCCESS;
    }
    case DC_PROOFS: {
        p.post(MultBC{v1, v2, v3, true}); // only use RUP justifications = true
        p.add_presolver(ProofAutoTable{{v1, v2, v3}});
        stats = solve(
            p, [&](const CurrentState &) -> bool { return false; }, make_optional(ProofOptions{"mult_experiment_gac.opb", "mult_experiment_gac.pbp"}));
        cout << stats.solve_time.count() << ",";

        auto start_time_dc = std::chrono::steady_clock::now();
        auto result_dc = system("veripb mult_experiment_gac.opb mult_experiment_gac.pbp >/dev/null");
        auto verify_time_bc = std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - start_time_dc).count();
        cout << verify_time_bc << ",";
        return result_dc == EXIT_SUCCESS;
    }
    }
}
auto run_mult_tests(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()             //
        ("help", "Display help information"); //

    po::options_description all_options{"All options"};

    all_options.add_options()(
        "n", po::value<int>()->default_value(200), "Total runs") //
        ;
    all_options.add_options()(
        "incr", po::value<int>()->default_value(1), "Increase domain range by") //
        ;
    all_options.add_options()(
        "r", po::value<int>()->default_value(1), "Increase every r repetitions.") //
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
    auto incr = options_vars["incr"].as<int>();
    auto r = options_vars["r"].as<int>();
    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>>> data = {};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    auto limit = 10;
    for (int x = 1; x < n + 1; ++x) {
        if (x % r == 0)
            limit += incr;

        generate_random_data(rand, data,
            random_bounds(-limit, limit, 0, limit),
            random_bounds(-limit, limit, 0, limit),
            random_bounds(-limit, limit, 0, limit));
    }
    cout << "xmin,xmax,ymin,ymax,zmin,zmax,noproofsolve,bcproofsolve,bcverify,gacproofsolve,gacverify" << endl;
    auto count = 1;
    for (auto & [r1, r2, r3] : data) {
        cout << r1.first << "," << r1.second << ","
             << r2.first << "," << r2.second << ","
             << r3.first << "," << r3.second << ",";
        cerr << "[" << count << "/" << n << "] " << r1.first << "," << r1.second << ","
             << r2.first << "," << r2.second << ","
             << r3.first << "," << r3.second << endl;

        run_mult_test(r1, r2, r3, NO_PROOFS);
        if (! run_mult_test(r1, r2, r3, DC_PROOFS))
            run_mult_test(r1, r2, r3, BC_PROOFS);
        if (! run_mult_test(r1, r2, r3, DC_PROOFS))
            return EXIT_FAILURE;

        cout << endl;
        count++;
    }

    return EXIT_SUCCESS;
}

auto run_fractions_test(int n, TestType test_type) -> bool
{
    auto rup_only = test_type == DC_PROOFS;
    Problem p;

    vector<SimpleIntegerVariableID> numerators{};
    vector<SimpleIntegerVariableID> denominators_first_digit{};
    vector<SimpleIntegerVariableID> denominators_second_digit{};
    vector<SimpleIntegerVariableID> denominators{};

    for (int i = 0; i < n; i++) {
        numerators.emplace_back(p.create_integer_variable(1_i, 9_i));
        denominators_first_digit.emplace_back(p.create_integer_variable(1_i, 9_i));
        denominators_second_digit.emplace_back(p.create_integer_variable(1_i, 9_i));
        denominators.emplace_back(p.create_integer_variable(1_i, 99_i));
    }
    vector<IntegerVariableID> digits(numerators.begin(), numerators.end());
    digits.insert(digits.end(), denominators_first_digit.begin(), denominators_first_digit.end());
    digits.insert(digits.end(), denominators_second_digit.begin(), denominators_second_digit.end());
    p.post(AllDifferent{digits});

    vector<SimpleIntegerVariableID> denominators_partial_products{};
    SimpleIntegerVariableID prev_product_var = p.create_integer_variable(1_i, 1_i);

    auto max_product_val = 100_i;
    for (unsigned int i = 0; i < denominators.size(); i++) {
        p.post(WeightedSum{} + 10_i * denominators_first_digit[i] + 1_i * denominators_second_digit[i] + -1_i * denominators[i] == 0_i);
        denominators_partial_products.emplace_back(p.create_integer_variable(1_i, max_product_val));
        p.post(MultBC{prev_product_var, denominators[i], denominators_partial_products[i], rup_only});
        if (rup_only)
            p.add_presolver(ProofAutoTable{{prev_product_var, denominators[i], denominators_partial_products[i]}});
        prev_product_var = denominators_partial_products[i];
        max_product_val = max_product_val * 100_i;
    }

    SimpleIntegerVariableID & denominators_product = denominators_partial_products[n - 1];
    vector<SimpleIntegerVariableID> numerator_multiplier{};
    vector<SimpleIntegerVariableID> summands{};
    WeightedSum frac_sum{};
    for (unsigned int i = 0; i < denominators.size(); i++) {
        numerator_multiplier.emplace_back(p.create_integer_variable(1_i, max_product_val / 100_i));
        summands.emplace_back(p.create_integer_variable(1_i, max_product_val / 10_i));
        p.post(MultBC{numerator_multiplier[i], denominators[i], denominators_product, rup_only});
        if (rup_only)
            p.add_presolver(ProofAutoTable{{numerator_multiplier[i], denominators[i], denominators_product}});
        p.post(MultBC{numerator_multiplier[i], numerators[i], summands[i], rup_only});
        if (rup_only)
            p.add_presolver(ProofAutoTable{{numerator_multiplier[i], numerators[i], summands[i]}});
        frac_sum += 1_i * summands[i];
        // Break symmetries
        if (i > 1)
            p.post(LessThan{numerators[i - 1], numerators[i]});
    }
    frac_sum += -1_i * denominators_product;
    p.post(frac_sum == 0_i);

    auto stats = Stats{};
    switch (test_type) {
    case NO_PROOFS:
        stats = solve_with(
            p,
            SolveCallbacks{
                .solution =
                    [&](const CurrentState & s) -> bool {
                    for (int i = 0; i < n; i++) {
                        cout << s(numerators[i]) << "    ";
                    }
                    cout << endl;

                    for (int i = 0; i < n - 1; i++) {
                        cout << "-- + ";
                    }
                    cout << "-- == 1" << endl;

                    for (int i = 0; i < n; i++) {
                        cout << s(denominators_first_digit[i]) << s(denominators_second_digit[i]) << "   ";
                    }
                    cout << endl;
                    return false;
                },
                .branch = branch_in_order(digits)},
            nullopt);
        if (stats.solutions == 0)
            cout << "UNSAT" << endl;
        cout << stats << endl;
        return true;
    case BC_PROOFS: {
        stats = solve_with(
            p,
            SolveCallbacks{
                .solution =
                    [&](const CurrentState & s) -> bool {
                    for (int i = 0; i < n; i++) {
                        cout << s(numerators[i]) << "    ";
                    }
                    cout << endl;

                    for (int i = 0; i < n - 1; i++) {
                        cout << "-- + ";
                    }
                    cout << "-- == 1" << endl;

                    for (int i = 0; i < n; i++) {
                        cout << s(denominators_first_digit[i]) << s(denominators_second_digit[i]) << "   ";
                    }
                    cout << endl;
                    return false;
                },
                .branch = branch_in_order(digits)},
            make_optional(ProofOptions{"mult_experiment_bc.opb", "mult_experiment_bc.pbp"}));
        cout << stats << endl;

        //        auto start_time_bc = std::chrono::steady_clock::now();
        //        auto result_bc = system("veripb mult_experiment_bc.opb mult_experiment_bc.pbp >/dev/null");
        //        auto verify_time_bc = std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - start_time_bc).count();
        //        cout << verify_time_bc << ",";
        //        return result_bc == EXIT_SUCCESS;
        return true;
    }
    case DC_PROOFS: {
        stats = solve_with(
            p,
            SolveCallbacks{
                .solution =
                    [&](const CurrentState & s) -> bool {
                    for (int i = 0; i < n; i++) {
                        cout << s(numerators[i]) << "    ";
                    }
                    cout << endl;

                    for (int i = 0; i < n - 1; i++) {
                        cout << "-- + ";
                    }
                    cout << "-- == 1" << endl;

                    for (int i = 0; i < n; i++) {
                        cout << s(denominators_first_digit[i]) << s(denominators_second_digit[i]) << "   ";
                    }
                    cout << endl;
                    return false;
                },
                .branch = branch_in_order(digits)},
            make_optional(ProofOptions{"mult_experiment_bc.opb", "mult_experiment_bc.pbp"}));
        cout << stats << endl;
        //        cout << stats.solve_time.count() << ",";
        //
        //        auto start_time_dc = std::chrono::steady_clock::now();
        //        auto result_dc = system("veripb mult_experiment_gac.opb mult_experiment_gac.pbp >/dev/null");
        //        auto verify_time_bc = std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - start_time_dc).count();
        //        cout << verify_time_bc << ",";
        //        return result_dc == EXIT_SUCCESS;
        return true;
    }
    }
}

auto run_fractions_tests(int argc, char * argv[])
{
    po::options_description display_options{"Program options"};
    display_options.add_options()             //
        ("help", "Display help information"); //

    po::options_description all_options{"All options"};

    all_options.add_options()(
        "n", po::value<int>()->default_value(3), "Total num fractions") //
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
    for (int i = 2; i <= 2; i++) {
        //        cout << i << ", " << endl;

        run_fractions_test(i, NO_PROOFS);
        if (! run_fractions_test(i, DC_PROOFS))
            return EXIT_FAILURE;
        //        if (! run_fractions_test(i, BC_PROOFS))
        //            return EXIT_FAILURE;
        cout << endl;
    }

    return EXIT_SUCCESS;
}
// Use this to test a specific instance
auto run_single() -> int
{
    Problem p;
    auto v1 = p.create_integer_variable(2_i, 6_i);
    auto v2 = p.create_integer_variable(-10_i, -2_i);
    auto v3 = p.create_integer_variable(-3_i, 4_i);
    p.post(MultBC{v1, v2, v3, true});
    p.add_presolver(ProofAutoTable{{v1, v2, v3}});
    solve(
        p, [&](const CurrentState &) -> bool { return false; }, make_optional(ProofOptions{"mult_bc.opb", "mult_bc.pbp"}));
    system("veripb --trace --traceFailed --useColor mult_bc.opb mult_bc.pbp");
    return EXIT_SUCCESS;
}

auto main(int argc, char * argv[]) -> int
{
    return run_fractions_tests(argc, argv);
    // return run_single();
}
