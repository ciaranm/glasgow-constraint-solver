// Measure the per-propagation cost of a single linear <= constraint.
//
// Post `copies` identical LinearLessThanEqual constraints over the same `len`
// variables. The copies are redundant, so the search tree is identical for any
// copies >= 1 (they all reach the same fixpoint), but every wake runs all of them
// -- so the propagation count scales with `copies`, and the slope
//   (time(copies) - time(1)) / (props(copies) - props(1))
// is the marginal cost of one constraint's propagation: its coarse wake plus one
// sweep. Select the sweep path with GCS_LINEAR_INCREMENTAL_THRESHOLD (0 =
// incremental/folded, a huge value = stateless).

#include <gcs/gcs.hh>

#include <chrono>
#include <cstdlib>
#include <vector>

#include <version>
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#endif

#include <cxxopts.hpp>

using namespace gcs;

using std::size_t;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("linear_prop_cost", "Per-propagation cost of a single linear <= constraint");
    options.add_options()                                                                              //
        ("vars", "Number of variables", cxxopts::value<int>()->default_value("120"))                   //
        ("domain", "Domain 0..d", cxxopts::value<int>()->default_value("30"))                          //
        ("len", "Variables in the constraint", cxxopts::value<int>()->default_value("60"))             //
        ("copies", "Redundant identical copies to post", cxxopts::value<int>()->default_value("1"))    //
        ("budget-num", "Budget numerator", cxxopts::value<int>()->default_value("70"))                 //
        ("budget-den", "Budget denominator", cxxopts::value<int>()->default_value("100"))              //
        ("cap", "Stop after this many solutions", cxxopts::value<long long>()->default_value("50000")) //
        ("help", "Display help");
    auto o = options.parse(argc, argv);
    if (o.contains("help")) {
        println("{}", options.help());
        return EXIT_SUCCESS;
    }
    int n = o["vars"].as<int>(), d = o["domain"].as<int>(), len = o["len"].as<int>(), copies = o["copies"].as<int>();
    int bn = o["budget-num"].as<int>(), bd = o["budget-den"].as<int>();
    long long cap = o["cap"].as<long long>();
    if (len > n)
        len = n;

    Problem p;
    auto vars = p.create_integer_variable_vector(static_cast<size_t>(n), 0_i, Integer{d});
    WeightedSum base;
    for (int i = 0; i < len; ++i)
        base += 1_i * vars[i];
    Integer budget{static_cast<long long>(len) * d * bn / bd};
    for (int k = 0; k < copies; ++k)
        p.post(LinearLessThanEqual{WeightedSum{base}, budget});

    long long sols = 0;
    auto start = std::chrono::steady_clock::now();
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return ++sols < cap; },
            .branch = branch_with(variable_order::in_order(vars), value_order::smallest_first())});
    auto elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();

    println("len={} copies={} recursions={} propagations={} wall={:.4f}s", len, copies, stats.recursions, stats.propagations, elapsed);
    return EXIT_SUCCESS;
}
