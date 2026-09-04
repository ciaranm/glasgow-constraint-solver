#include <gcs/constraints/linear.hh>
#include <gcs/gcs.hh>

#include <examples/benchmark_cli.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <string>
#include <vector>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

#include <cxxopts.hpp>

using namespace gcs;

using std::cerr;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::string;
using std::uniform_int_distribution;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

// A random CSP of linear equalities, to exercise the *tabulated* extensional
// propagator on tables that tabulation actually builds. This is the shape the
// `.tbl` suite does not cover: every table there is posted by the user through
// `Table`, where the tuples are given, whereas these are derived in-proof by
// build_table_in_proof() from a relation.
//
// Size is what makes it useful. A `k`-term equality enumerates all but the
// determined variable, so the table holds up to `domain^(k-1)` tuples --
// `--terms 4 --domain 12` gives 1 728, which is the regime where the compact
// table pays, and which `consistency::Auto` will not reach on its own:
// want_tabulation's budget is default_tabulation_threshold(), 100 by default,
// so arithmetic constraints under Auto tabulate at most ~100 tuples and never
// clear ExtensionalCompactTable::min_tuples. Tabulated GAC linear equality,
// asked for explicitly, is the constraint that gets there.
//
// Fixed (deterministic) search, so the tree is identical between consistency
// levels and between algorithms -- the interesting number is solve time.
auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("tabulated_linear_random", "Random tabulated-linear-equality benchmark");
    options.add_options()                                                                          //
        ("vars", "Number of variables", cxxopts::value<int>()->default_value("24"))                //
        ("domain", "Domain size (values 0..domain-1)", cxxopts::value<int>()->default_value("12")) //
        ("constraints", "Number of linear equalities", cxxopts::value<int>()->default_value("14")) //
        ("terms", "Variables per equality", cxxopts::value<int>()->default_value("4"))             //
        ("coefficient", "Coefficients are drawn from -this..this, excluding 0",                    //
            cxxopts::value<int>()->default_value("3"))                                             //
        ("consistency", "Linear equality consistency: tabulated or bc",                            //
            cxxopts::value<string>()->default_value("tabulated"))                                  //
        ("seed", "Random seed", cxxopts::value<unsigned>()->default_value("1"))                    //
        ("first", "Stop at the first solution instead of enumerating all")                         //
        ("timeout", "Timeout in seconds (0 = none)", cxxopts::value<double>()->default_value("0")) //
        ("help", "Display help");
    auto options_vars = options.parse(argc, argv);
    if (options_vars.contains("help")) {
        println("{}", options.help());
        return EXIT_SUCCESS;
    }

    auto n = options_vars["vars"].as<int>();
    auto d = options_vars["domain"].as<int>();
    auto m = options_vars["constraints"].as<int>();
    auto k = options_vars["terms"].as<int>();
    auto max_coeff = options_vars["coefficient"].as<int>();
    auto seed = options_vars["seed"].as<unsigned>();
    auto first_only = options_vars.contains("first");

    // Tabulated is the point of the benchmark; bc is the comparison, and is what
    // LinearEquality does by default.
    auto level = LinearEqualityConsistency{consistency::Tabulated{}};
    if (auto choice = options_vars["consistency"].as<string>(); "bc" == choice)
        level = consistency::BC{};
    else if ("tabulated" != choice) {
        println(cerr, "Error: --consistency must be tabulated or bc");
        return EXIT_FAILURE;
    }

    if (k < 2 || k > n) {
        println(cerr, "Error: --terms must be at least 2 and at most --vars");
        return EXIT_FAILURE;
    }

    mt19937 rng(seed);
    uniform_int_distribution<int> pick_var(0, n - 1);
    uniform_int_distribution<int> pick_coeff(1, max_coeff);
    uniform_int_distribution<int> pick_sign(0, 1);
    uniform_int_distribution<int> pick_value(0, d - 1);

    Problem p;
    auto vars = p.create_integer_variable_vector(static_cast<size_t>(n), 0_i, Integer{d - 1});

    for (int c = 0; c < m; ++c) {
        // k distinct variables.
        vector<int> chosen;
        while (static_cast<int>(chosen.size()) < k) {
            int v = pick_var(rng);
            if (chosen.end() == std::find(chosen.begin(), chosen.end(), v))
                chosen.push_back(v);
        }

        // The right hand side is the value of a random assignment, so each
        // equality is satisfiable on its own and the instance is tight rather
        // than trivially unsatisfiable.
        WeightedSum sum;
        Integer rhs = 0_i;
        for (int t = 0; t < k; ++t) {
            Integer coeff{pick_sign(rng) ? pick_coeff(rng) : -pick_coeff(rng)};
            sum += coeff * vars[static_cast<size_t>(chosen[static_cast<size_t>(t)])];
            rhs += coeff * Integer{pick_value(rng)};
        }
        p.post(LinearEquality{move(sum), rhs}.with_consistency(level));
    }

    unsigned long long solutions = 0;
    auto stats = bench::solve_with_timeout(options_vars["timeout"].as<double>(), p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           ++solutions;
                           return ! first_only;
                       },
            .branch = branch_with(variable_order::dom_then_deg(p), value_order::smallest_first())});

    println("solutions: {}", solutions);
    println("recursions: {}", stats.recursions);
    println("failures: {}", stats.failures);
    println("propagations: {}", stats.propagations);
    println("solveTime: {:.3f}", std::chrono::duration_cast<std::chrono::milliseconds>(stats.solve_time).count() / 1000.0);
    return EXIT_SUCCESS;
}
