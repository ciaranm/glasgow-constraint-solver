// Benchmark for the length at which a clause should watch two literals rather
// than scan them all (issue #1060).
//
// A random set cover: each of --clauses elements is covered by --length of the
// --vars sets, chosen at random, which is the clause "at least one of these
// sets is chosen", and at most --budget sets may be chosen. The search takes
// the sets in order and tries leaving each one out first, which is the scan's
// worst case: every clause over a set it has left out wakes, and walks the
// literals that the search has already made false to find the undecided ones.
// It enumerates covers until the node limit, so that every length does the
// same amount of search.
//
// The constraints, branching and node limit are fixed, so the search tree is
// the same whatever the threshold: compare recursions, which must match, then
// instructions or time. For example, to compare the two paths at one length:
//   clause_watch_bench --length 32 --watch-threshold 0
//   clause_watch_bench --length 32 --watch-threshold 1000000

#include <gcs/gcs.hh>

#include <chrono>
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
using std::optional;
using std::size_t;
using std::uniform_int_distribution;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("clause_watch_bench", "Benchmark for the clause watch threshold");
    options.add_options()                                                                                    //
        ("vars", "Number of sets", cxxopts::value<int>()->default_value("200"))                              //
        ("clauses", "Number of elements to cover", cxxopts::value<int>()->default_value("400"))              //
        ("length", "Sets covering each element", cxxopts::value<int>()->default_value("16"))                 //
        ("budget", "Most sets that may be chosen", cxxopts::value<int>()->default_value("40"))               //
        ("nodes", "Stop after this many search nodes", cxxopts::value<long long>()->default_value("200000")) //
        ("watch-threshold", "Clause watch threshold (default: the solver's)", cxxopts::value<size_t>())      //
        ("seed", "RNG seed", cxxopts::value<unsigned>()->default_value("1"))                                 //
        ("help", "Display help");
    auto o = options.parse(argc, argv);
    if (o.contains("help")) {
        println("{}", options.help());
        return EXIT_SUCCESS;
    }
    int n = o["vars"].as<int>(), m = o["clauses"].as<int>(), length = o["length"].as<int>(), budget = o["budget"].as<int>();
    long long node_limit = o["nodes"].as<long long>();
    optional<size_t> threshold;
    if (o.contains("watch-threshold"))
        threshold = o["watch-threshold"].as<size_t>();
    unsigned seed = o["seed"].as<unsigned>();
    if (length > n)
        length = n;

    mt19937 rng(seed);
    uniform_int_distribution<int> pick(0, n - 1);

    Problem p;
    auto sets = p.create_integer_variable_vector(static_cast<size_t>(n), 0_i, 1_i);
    for (int c = 0; c < m; ++c) {
        vector<bool> used(n, false);
        vector<IntegerVariableID> covering;
        while (static_cast<int>(covering.size()) < length) {
            int j = pick(rng);
            if (used[j])
                continue;
            used[j] = true;
            covering.push_back(sets[j]);
        }
        p.post(Or{covering}.with_watch_threshold(threshold));
    }
    WeightedSum chosen;
    for (auto & s : sets)
        chosen += 1_i * s;
    p.post(LinearLessThanEqual{chosen, Integer{budget}});

    long long solutions = 0, nodes = 0;
    auto start = std::chrono::steady_clock::now();
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return ++solutions, true; },
            .trace = [&](const CurrentState &) -> bool { return ++nodes < node_limit; },
            .branch = branch_with(variable_order::in_order(sets), value_order::smallest_first())});
    auto elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();

    println("vars={} clauses={} length={} budget={} nodes={} threshold={} seed={}", n, m, length, budget, node_limit,
        threshold ? std::to_string(*threshold) : "default", seed);
    println("solutions={} recursions={} propagations={} wall={:.3f}s", solutions, stats.recursions, stats.propagations, elapsed);
    return EXIT_SUCCESS;
}
