// Wall-clock benchmark for slack-based waking of long linear inequalities.
//
// Builds a batch of long, loose Sum(c_i x_i) <= budget constraints with
// mismatched coefficients (a few large, many small) over a shared pool of
// variables, then enumerates solutions up to a cap. The search tree is identical
// whichever linear propagation path is used -- the constraints, branching, and
// cap are fixed -- so this isolates the per-node cost of the propagator.
//
// Select the path via the environment (read once at start-up), then compare the
// wall-clock this prints. recursions must match across all three:
//   coarse-stateless : GCS_LINEAR_INCREMENTAL_THRESHOLD=1000000
//   incremental      : GCS_LINEAR_INCREMENTAL_THRESHOLD=0
//   slack-watched    : GCS_LINEAR_SLACK_WATCH_THRESHOLD=0 GCS_LINEAR_SLACK_WATCH_COVER_PERCENT=100
// (the last also honours the incremental threshold for any direction it declines).

#include <gcs/gcs.hh>

#include <chrono>
#include <cstdlib>
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
using std::size_t;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("linear_slack_bench", "Wall-clock benchmark for slack-based linear-inequality waking");
    options.add_options()                                                                                  //
        ("vars", "Number of variables", cxxopts::value<int>()->default_value("120"))                       //
        ("domain", "Domain 0..d", cxxopts::value<int>()->default_value("30"))                              //
        ("sums", "Number of sum-<= constraints", cxxopts::value<int>()->default_value("120"))              //
        ("sumlen", "Variables per sum", cxxopts::value<int>()->default_value("60"))                        //
        ("big", "How many terms per sum get a big coefficient", cxxopts::value<int>()->default_value("3")) //
        ("budget-num", "Budget numerator", cxxopts::value<int>()->default_value("55"))                     //
        ("budget-den", "Budget denominator", cxxopts::value<int>()->default_value("100"))                  //
        ("cap", "Stop after this many solutions", cxxopts::value<long long>()->default_value("20000"))     //
        ("seed", "RNG seed", cxxopts::value<unsigned>()->default_value("1"))                               //
        ("help", "Display help");
    auto o = options.parse(argc, argv);
    if (o.contains("help")) {
        println("{}", options.help());
        return EXIT_SUCCESS;
    }
    int n = o["vars"].as<int>(), d = o["domain"].as<int>(), nsums = o["sums"].as<int>(), sumlen = o["sumlen"].as<int>();
    int big = o["big"].as<int>(), bn = o["budget-num"].as<int>(), bd = o["budget-den"].as<int>();
    long long cap = o["cap"].as<long long>();
    unsigned seed = o["seed"].as<unsigned>();
    if (sumlen > n)
        sumlen = n;

    mt19937 rng(seed);
    std::uniform_int_distribution<int> pick(0, n - 1);

    Problem p;
    auto vars = p.create_integer_variable_vector(static_cast<size_t>(n), 0_i, Integer{d});
    for (int c = 0; c < nsums; ++c) {
        vector<bool> used(n, false);
        WeightedSum sum;
        int placed = 0;
        Integer worst{0};
        while (placed < sumlen) {
            int j = pick(rng);
            if (used[j])
                continue;
            used[j] = true;
            // A few big coefficients, the rest small: a mismatched spread, so the
            // covering set is dominated by the big terms.
            Integer coeff = (placed < big) ? Integer{10 + (placed * 7)} : 1_i;
            sum += coeff * vars[j];
            worst += coeff * Integer{d};
            ++placed;
        }
        Integer budget{worst.raw_value * bn / bd};
        p.post(LinearLessThanEqual{sum, budget});
    }

    long long solutions = 0;
    auto start = std::chrono::steady_clock::now();
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return ++solutions < cap; },
            .branch = branch_with(variable_order::in_order(vars), value_order::smallest_first())});
    auto elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();

    println("vars={} domain=0..{} sums={} sumlen={} big={} budget={}/{} cap={} seed={}", n, d, nsums, sumlen, big, bn, bd, cap, seed);
    println("solutions={} recursions={} propagations={} wall={:.3f}s", solutions, stats.recursions, stats.propagations, elapsed);
    return EXIT_SUCCESS;
}
