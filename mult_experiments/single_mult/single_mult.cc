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

auto run_mult_test(pair<int, int> v1_range, pair<int, int> v2_range, pair<int, int> v3_range, TestType test_type, const string & proof_prefix) -> bool
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
            p, [&](const CurrentState &) -> bool { return false; }, make_optional(ProofOptions{proof_prefix + "_bc.opb", proof_prefix + "_bc.pbp"}));
        cout << stats.solve_time.count() << ",";

        auto vpb_command = "timeout 1000s veripb " + proof_prefix + "_bc.opb " + proof_prefix + "_bc.pbp >/dev/null";
        auto result_bc = system(vpb_command.c_str());
        auto start_time_bc = std::chrono::steady_clock::now();
        auto verify_time_bc = std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - start_time_bc).count();
        cout << verify_time_bc << ",";
        return result_bc == EXIT_SUCCESS;
    }
    case DC_PROOFS: {
        p.post(MultBC{v1, v2, v3, true}); // only use RUP justifications = true
        p.add_presolver(ProofAutoTable{{v1, v2, v3}});
        stats = solve(
            p, [&](const CurrentState &) -> bool { return false; }, make_optional(ProofOptions{proof_prefix + "_dc.opb", proof_prefix + "_dc.pbp"}));
        cout << stats.solve_time.count() << ",";

        auto vpb_command = "timeout 1000s veripb " + proof_prefix + "_dc.opb " + proof_prefix + "_dc.pbp >/dev/null";
        auto result_bc = system(vpb_command.c_str());

        auto start_time_dc = std::chrono::steady_clock::now();
        auto result_dc = system(vpb_command.c_str());
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
    ;
    all_options.add_options()(
        "proof", po::value<string>()->default_value("./mult_test"), "Increase every r repetitions.") //
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
    auto proof = options_vars["proof"].as<string>();
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

        run_mult_test(r1, r2, r3, NO_PROOFS, proof);
        if (! run_mult_test(r1, r2, r3, BC_PROOFS, proof))
            return EXIT_FAILURE;
        if (! run_mult_test(r1, r2, r3, DC_PROOFS, proof))
            return EXIT_FAILURE;

        cout << endl;
        count++;
    }

    return EXIT_SUCCESS;
}

// Use this to test a specific instance (debugging)
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
    return run_mult_tests(argc, argv);
    // return run_single();
}
