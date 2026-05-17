// Benchmark harness for comparing the new Knapsack against KnapsackLegacy.
// Posts the same problem with one or the other and prints solver stats.
// Branching is fully deterministic so that recursions / propagations
// should match exactly between the two propagators on a given instance.
//
// CLI:
//   --legacy             Post KnapsackLegacy (default: Knapsack)
//   --instance N         Pick an instance from the curated set (1..4)
//   --prove              Generate a proof
//   --proof-files-basename PATH  (default: "knapsack_bench")
//   --stats              Print solver stats (default: on; flag kept for
//                        compatibility with the harness)
//
// This file is intentionally not part of any ctest target.

#include <gcs/constraints/knapsack.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

#include <cxxopts.hpp>

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
using std::make_optional;
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

namespace
{
    struct Instance
    {
        const char * name;
        vector<vector<Integer>> coeffs;
        Integer item_lo;
        Integer item_hi;
        size_t n_items;
        vector<std::pair<Integer, Integer>> total_bounds;
        bool optimise_max_first_total;
    };

    auto curated_instance(int n) -> Instance
    {
        switch (n) {
        case 1:
            // 10 items 0/1, k=2 (weight/profit), tight bounds.
            return Instance{
                "i1_10_01_k2_enum",
                {{3_i, 4_i, 2_i, 5_i, 3_i, 4_i, 2_i, 3_i, 5_i, 2_i},
                    {4_i, 2_i, 3_i, 5_i, 2_i, 4_i, 3_i, 2_i, 3_i, 5_i}},
                0_i, 1_i, 10,
                {{12_i, 20_i}, {14_i, 24_i}},
                false};
        case 2:
            // 10 items 0/1, k=2 with wider coefficients (1..8) — bigger
            // static DAG per coordinate while keeping the same number of
            // items as inst 1, so we can isolate scaffolding-size effects.
            return Instance{
                "i2_10_01_k2_wide",
                {{2_i, 7_i, 3_i, 8_i, 1_i, 6_i, 4_i, 5_i, 3_i, 7_i},
                    {6_i, 2_i, 8_i, 1_i, 5_i, 3_i, 7_i, 4_i, 6_i, 2_i}},
                0_i, 1_i, 10,
                {{20_i, 32_i}, {22_i, 36_i}},
                false};
        case 3:
            // 7 items domain 0..2, k=2 — non-binary items.
            return Instance{
                "i3_7_0to2_k2_enum",
                {{2_i, 3_i, 1_i, 2_i, 3_i, 2_i, 1_i},
                    {3_i, 1_i, 2_i, 3_i, 2_i, 1_i, 2_i}},
                0_i, 2_i, 7,
                {{8_i, 14_i}, {10_i, 16_i}},
                false};
        case 4:
            // 9 items 0/1, k=3 totals.
            return Instance{
                "i4_9_01_k3_enum",
                {{3_i, 4_i, 2_i, 5_i, 3_i, 4_i, 2_i, 3_i, 5_i},
                    {4_i, 2_i, 3_i, 5_i, 2_i, 4_i, 3_i, 2_i, 3_i},
                    {2_i, 5_i, 3_i, 4_i, 5_i, 2_i, 4_i, 3_i, 4_i}},
                0_i, 1_i, 9,
                {{10_i, 18_i}, {12_i, 22_i}, {11_i, 19_i}},
                false};
        default:
            println(cerr, "unknown instance {}", n);
            std::exit(EXIT_FAILURE);
        }
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Knapsack benchmark harness");
    cxxopts::ParseResult vars;

    try {
        options.add_options("Program options")                                                 //
            ("help", "Display help information")                                               //
            ("legacy", "Post KnapsackLegacy instead of Knapsack")                              //
            ("instance", "Curated instance number (1..4)", cxxopts::value<int>())              //
            ("prove", "Generate a proof")                                                      //
            ("proof-files-basename", "Basename for .opb and .pbp files",                       //
                cxxopts::value<string>()->default_value("knapsack_bench"))                     //
            ("stats", "Print solver stats")                                                    //
            ("root-only", "Abort after the first complete propagation (measures init + first prop)");
        vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "{}", e.what());
        return EXIT_FAILURE;
    }

    if (vars.contains("help") || ! vars.contains("instance")) {
        println("{}", options.help());
        return EXIT_SUCCESS;
    }

    auto inst = curated_instance(vars["instance"].as<int>());
    bool legacy = vars.contains("legacy");

    Problem p;
    auto items = p.create_integer_variable_vector(inst.n_items, inst.item_lo, inst.item_hi, "item");
    vector<IntegerVariableID> totals;
    totals.reserve(inst.total_bounds.size());
    for (size_t x = 0; x < inst.total_bounds.size(); ++x)
        totals.push_back(p.create_integer_variable(inst.total_bounds[x].first,
            inst.total_bounds[x].second, "t" + std::to_string(x)));

    if (legacy)
        p.post(KnapsackLegacy{inst.coeffs, items, totals});
    else
        p.post(Knapsack{inst.coeffs, items, totals});

    if (inst.optimise_max_first_total)
        p.maximise(totals[0]);

    bool root_only = vars.contains("root-only");
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool { return true; },
            .trace = [&](const CurrentState &) -> bool { return ! root_only; },
            .branch = branch_with(variable_order::dom_then_deg(items), value_order::smallest_first())},
        vars.contains("prove")
            ? make_optional<ProofOptions>(vars["proof-files-basename"].as<string>())
            : nullopt);

    print("{}", stats);
    return EXIT_SUCCESS;
}
