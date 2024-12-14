#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <string>

#include <boost/program_options.hpp>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/mult_bc.hh>
#include <gcs/constraints/not_equals.hh>
#include <mult_experiments/mult_experiments_utils.hh>
#include <optional>

using namespace gcs;
using namespace gcs::test_innards;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::optional;
using std::string;
using std::vector;

namespace po = boost::program_options;

auto constrain_digit_sum(Problem & p, vector<SimpleIntegerVariableID> digits, SimpleIntegerVariableID number)
{
    WeightedSum wsum{};
    for (unsigned int i = 0; i < digits.size(); i++) {
        wsum += Integer{(long)pow(10, i)} * digits[i];
    }
    wsum += -1_i * number;
    p.post(wsum == 0_i);
}

auto run_skeleton_puzzle(int a, int b, vector<vector<bool>> pos, MultTestType test_type, const string & proof_prefix) -> void
{
    auto rup_only = test_type == DC_PROOFS;
    Problem p;
    IntegerVariableID k_var = 0_c;

    vector<SimpleIntegerVariableID> a_digits{};
    for (int i = 0; i < a; i++) {
        a_digits.emplace_back(p.create_integer_variable(0_i, 9_i));
        p.post(NotEquals(a_digits[i], k_var));
    }

    SimpleIntegerVariableID a_var = p.create_integer_variable(0_i, Integer{(long)pow(10, a)});
    constrain_digit_sum(p, a_digits, a_var);

    vector<SimpleIntegerVariableID> b_digits{};
    for (int i = 0; i < b; i++) {
        b_digits.emplace_back(p.create_integer_variable(0_i, 9_i));
        p.post(NotEquals(b_digits[i], k_var));
    }

    vector<vector<SimpleIntegerVariableID>> partial_product_digits{};
    vector<SimpleIntegerVariableID> partial_product{};
    for (int i = 0; i < b; i++) {
        partial_product_digits.emplace_back();
        partial_product.emplace_back(p.create_integer_variable(0_i, Integer{(long)pow(10, a + 1)}));
        for (int j = 0; j < a + 1; j++) {
            partial_product_digits[i].emplace_back(p.create_integer_variable(0_i, 9_i));
            if (pos[i][a - j]) {
                p.post(Equals(partial_product_digits[i][j], k_var));
            }
            else {
                p.post(NotEquals(partial_product_digits[i][j], k_var));
            }
        }
        constrain_digit_sum(p, partial_product_digits[i], partial_product[i]);
        p.post(MultBC{a_var, b_digits[i], partial_product[i], rup_only});
    }

    vector<SimpleIntegerVariableID> c_digits{};
    auto c_var = p.create_integer_variable(0_i, Integer{(long)pow(10, a + b)});
    for (int i = 0; i < a + b; i++) {
        c_digits.emplace_back(p.create_integer_variable(0_i, 9_i));
        if (pos[b][a + b - 1 - i]) {

            p.post(Equals(c_digits[i], k_var));
        }
        else {

            p.post(NotEquals(c_digits[i], k_var));
        }
    }
    cout << endl;

    constrain_digit_sum(p, c_digits, c_var);
    constrain_digit_sum(p, partial_product, c_var);

    auto solution_callback = [&](const CurrentState & s) -> bool {
        for (int i = b - 1; i > -1; i--)
            cout << " ";
        for (int i = a - 1; i > -1; i--)
            cout << s(a_digits[i]);
        cout << endl;
        for (int i = 0; i < b + (a - b - 2); i++)
            cout << " ";
        cout << "x ";
        for (int i = b - 1; i > -1; i--)
            cout << s(b_digits[i]);
        cout << endl;
        for (int i = 0; i < a + b; i++)
            cout << "-";
        cout << endl;
        for (int i = 0; i < b; i++) {
            for (int j = 0; j < b - i - 1; j++)
                cout << " ";
            for (int j = a; j > -1; j--)
                cout << s(partial_product_digits[i][j]);
            cout << endl;
        }
        for (int i = 0; i < a + b; i++)
            cout << "-";
        cout << endl;
        for (int i = a + b - 1; i > -1; i--)
            cout << s(c_digits[i]);
        cout << endl
             << endl;
        return true;
    };

    switch (test_type) {
    case NO_PROOFS: {
        auto stats = solve_with(
            p,
            SolveCallbacks{
                .solution = solution_callback},
            nullopt);

        if (stats.solutions == 0)
            cout << "UNSAT" << endl;
        cout << stats << endl;
        return;
    }
    case BC_PROOFS: {
        auto stats = solve_with(
            p,
            SolveCallbacks{
                .solution = solution_callback},
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
        auto stats = solve_with_timeout(
            p,
            SolveCallbacks{
                .solution = solution_callback},
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
    display_options.add_options()            //
        ("help", "Display help information") //
        ("prove", "Create a proof");         //

    po::options_description all_options{"All options"};

    all_options.add(display_options);
    po::variables_map options_vars;

    all_options.add_options()(
        "proof", po::value<string>()->default_value("./skeleton"), "Proof file prefix") //
        ;

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

    auto proof = options_vars["proof"].as<string>();

    vector<vector<bool>> k_vector =
        {{1, 0, 0, 0, 0, 0, 0, 0},
            {0, 0, 1, 0, 1, 0, 0, 0},
            {0, 0, 0, 1, 1, 0, 0, 0},
            {0, 0, 0, 0, 1, 0, 0, 0},
            {0, 0, 0, 0, 0, 1, 1, 0},
            {0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0}};

    cout << "Without proofs:" << endl;
    run_skeleton_puzzle(7, 5, k_vector, NO_PROOFS, proof);
    cout << "With BC proofs:" << endl;
    run_skeleton_puzzle(7, 5, k_vector, BC_PROOFS, proof);
    cout << "With DC proofs:" << endl;
    run_skeleton_puzzle(7, 5, k_vector, DC_PROOFS, proof);
    cout << endl;

    return EXIT_SUCCESS;
}
