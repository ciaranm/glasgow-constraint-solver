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
#include <mult_experiments/mult_experiments_utils.hh>
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

auto run_fractions_test(int n, MultTestType test_type, const string & proof_prefix) -> void
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

    auto solution_callback = [&](const CurrentState & s) -> bool {
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
    };

    switch (test_type) {
    case NO_PROOFS:
        stats = solve_with(
            p,
            SolveCallbacks{
                .solution = solution_callback,
                .branch = branch_with(variable_order::in_order(digits), value_order::smallest_first())},
            nullopt);

        if (stats.solutions == 0)
            cout << "UNSAT" << endl;
        cout << stats << endl;
        return;
    case BC_PROOFS: {
        stats = solve_with(
            p,
            SolveCallbacks{
                .solution = solution_callback,
                .branch = branch_with(variable_order::in_order(digits), value_order::smallest_first())},
            make_optional(ProofOptions{proof_prefix + "_bc"}));

        cout << stats << endl;

        auto start_time_bc = std::chrono::steady_clock::now();
        string vpb_command = "veripb " + proof_prefix + "_bc.opb " + proof_prefix + "_bc.pbp --progressBar --stats";
        system(vpb_command.c_str());
        auto verify_time_bc = std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - start_time_bc).count();
        cout << "verification time: " << verify_time_bc << ",";
        return;
    }
    case DC_PROOFS: {
        stats = solve_with_timeout(
            p,
            SolveCallbacks{
                .solution = solution_callback,
                .branch = branch_with(variable_order::in_order(digits), value_order::smallest_first())},
            make_optional(ProofOptions{proof_prefix + "_dc"}), 32400);
        cout << stats << endl;
        cout << stats.solve_time.count() << ",";
        string vpb_command = "veripb " + proof_prefix + "_dc.opb " + proof_prefix + "_dc.pbp --progressBar --stats";
        auto start_time_dc = std::chrono::steady_clock::now();
        system(vpb_command.c_str());
        auto verify_time_dc = std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - start_time_dc).count();
        cout << "verification time: " << verify_time_dc << ",";
        return;
    }
    }
}

auto main(int argc, char * argv[]) -> int
{
    po::options_description display_options{"Program options"};
    display_options.add_options()             //
        ("help", "Display help information"); //

    po::options_description all_options{"All options"};

    all_options.add_options()(
        "proof", po::value<string>()->default_value("./fractions"), "Proof file prefix") //
        ;
    all_options.add_options()(
        "n", po::value<int>()->default_value(2), "Num fractions") //
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
    auto proof = options_vars["proof"].as<string>();
    cout << "Without proofs:" << endl;
    run_fractions_test(n, NO_PROOFS, proof);
    cout << "With BC proofs:" << endl;
    run_fractions_test(n, BC_PROOFS, proof);
    cout << "With DC proofs:" << endl;
    run_fractions_test(n, DC_PROOFS, proof);
    cout << endl;

    return EXIT_SUCCESS;
}
