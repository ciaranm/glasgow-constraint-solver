#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/mult_bc.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cxxopts.hpp>

#include <cstdlib>
#include <iostream>
#include <random>
#include <string>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("N_fractions Example");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program Options")                                                       //
            ("help", "Display help information")                                                     //
            ("prove", "Create a proof")                                                              //
            ("proof-files-basename", "Basename for the .opb and .pbp files",                         //
                cxxopts::value<string>()->default_value("n_fractions"))                              //
            ("stats", "Print solve statistics")                                                      //
            ;

        options.add_options()                                                                   //
            ("size", "Size of the problem to solve", cxxopts::value<int>()->default_value("2")) //
            ("unsat", "Exclude known solution for 2 fractions to make an UNSAT proof.")         //
            ;

        options.parse_positional({"size"});
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

    auto n = options_vars["size"].as<int>();

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
        p.post(MultBC{prev_product_var, denominators[i], denominators_partial_products[i]});
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
        p.post(MultBC{numerator_multiplier[i], denominators[i], denominators_product});
        p.post(MultBC{numerator_multiplier[i], numerators[i], summands[i]});
        frac_sum += 1_i * summands[i];
        // Break symmetries
        if (i > 0)
            p.post(LessThan{numerators[i - 1], numerators[i]});
    }
    frac_sum += -1_i * denominators_product;
    p.post(frac_sum == 0_i);
    if (options_vars.contains("unsat") && n == 2) {
        p.post(NotEquals(numerators[0], 8_c));
        p.post(NotEquals(numerators[1], 9_c));
        p.post(NotEquals(denominators[0], 26_c));
        p.post(NotEquals(denominators[1], 13_c));
    }

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
        return true;
    };

    auto stats = solve(
        p, solution_callback,
        options_vars.contains("prove")
            ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>())
            : nullopt);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
