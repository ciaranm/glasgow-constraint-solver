#include <gcs/constraints/table/negative_table.hh>
#include <gcs/gcs.hh>

#include <examples/benchmark_cli.hh>

#include <cstdlib>
#include <optional>
#include <random>
#include <vector>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#endif

#include <cxxopts.hpp>

using namespace gcs;

using std::mt19937;
using std::nullopt;
using std::optional;
using std::uniform_int_distribution;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

// A random binary-CSP benchmark built entirely from NegativeTable (forbidden
// tuples), to exercise the negative-table propagator: n variables of domain
// 0..d-1, and `constraints` random binary forbidden-tuple tables, each forbidding
// each of the d*d value pairs independently with probability `tightness`. Fixed
// (deterministic) search, so the search tree is identical regardless of how the
// propagator is triggered -- the interesting number is solve time / time-per-node.
auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("negative_table_random", "Random forbidden-tuple (NegativeTable) benchmark");
    options.add_options()                                                                                          //
        ("vars", "Number of variables", cxxopts::value<int>()->default_value("30"))                                //
        ("domain", "Domain size (values 0..domain-1)", cxxopts::value<int>()->default_value("12"))                 //
        ("constraints", "Number of binary forbidden-tuple tables", cxxopts::value<int>()->default_value("180"))    //
        ("tightness", "Probability each value pair is forbidden", cxxopts::value<double>()->default_value("0.34")) //
        ("seed", "Random seed", cxxopts::value<unsigned>()->default_value("1"))                                    //
        ("first", "Stop at the first solution instead of enumerating all")                                         //
        ("timeout", "Timeout in seconds (0 = none)", cxxopts::value<double>()->default_value("0"))                 //
        ("help", "Display help");
    auto options_vars = options.parse(argc, argv);
    if (options_vars.contains("help")) {
        println("{}", options.help());
        return EXIT_SUCCESS;
    }

    auto n = options_vars["vars"].as<int>();
    auto d = options_vars["domain"].as<int>();
    auto m = options_vars["constraints"].as<int>();
    auto tightness = options_vars["tightness"].as<double>();
    auto seed = options_vars["seed"].as<unsigned>();
    auto first_only = options_vars.contains("first");

    mt19937 rng(seed);
    uniform_int_distribution<int> pick_var(0, n - 1);
    std::uniform_real_distribution<double> unit(0.0, 1.0);

    Problem p;
    auto vars = p.create_integer_variable_vector(static_cast<size_t>(n), 0_i, Integer{d - 1});

    for (int c = 0; c < m; ++c) {
        int a = pick_var(rng), b = pick_var(rng);
        while (b == a)
            b = pick_var(rng);
        SimpleTuples forbidden;
        for (int u = 0; u < d; ++u)
            for (int v = 0; v < d; ++v)
                if (unit(rng) < tightness)
                    forbidden.push_back({Integer{u}, Integer{v}});
        if (! forbidden.empty())
            p.post(NegativeTable{{vars[a], vars[b]}, move(forbidden)});
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
