// Benchmark harness for the BinPacking propagator. Posts a curated instance
// and prints solver stats. Branching is fully deterministic so that solve
// trajectories are reproducible across propagator changes.
//
// CLI:
//   --instance N         Pick an instance from the curated set (1..6)
//   --bounds-only        Force bounds-only (skip Stage 3 DAG sweep)
//   --upfront            Use the opt-in upfront Stage 3 proof scaffolding
//                        (default is the per-call strategy)
//   --prove              Generate a proof
//   --proof-files-basename PATH  (default: "bin_packing_bench")
//   --root-only          Abort after first complete propagation (init + first prop)
//
// This file is intentionally not part of any ctest target.

#include <gcs/constraints/bin_packing.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <string>
#include <variant>
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
using std::make_optional;
using std::nullopt;
using std::string;
using std::variant;
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
        vector<Integer> sizes;
        vector<std::pair<Integer, Integer>> item_ranges; // per-item dom
        // For variable-load form: per-bin (lo, hi) of the load var.
        // For constant-cap form: just the cap.
        variant<vector<std::pair<Integer, Integer>>, vector<Integer>> bins;
    };

    auto curated_instance(int n) -> Instance
    {
        auto items = [](size_t count, int hi) { return vector<std::pair<Integer, Integer>>(count, {0_i, Integer{hi}}); };
        switch (n) {
        case 1:
            // 10 items / 3 bins, modest cap. Constant-cap form.
            return Instance{"i1_10_3bins_capa", {3_i, 4_i, 2_i, 5_i, 3_i, 4_i, 2_i, 3_i, 5_i, 2_i}, items(10, 2), vector<Integer>{12_i, 12_i, 12_i}};
        case 2:
            // 10 items / 3 bins variable-load, same sizes as inst 1.
            return Instance{"i2_10_3bins_load", {3_i, 4_i, 2_i, 5_i, 3_i, 4_i, 2_i, 3_i, 5_i, 2_i}, items(10, 2),
                vector<std::pair<Integer, Integer>>{{8_i, 14_i}, {8_i, 14_i}, {8_i, 14_i}}};
        case 3:
            // 12 items / 4 bins, wider per-bin cap, constant-cap.
            return Instance{"i3_12_4bins_capa_wide", {1_i, 2_i, 3_i, 4_i, 5_i, 2_i, 3_i, 4_i, 1_i, 2_i, 5_i, 3_i}, items(12, 3),
                vector<Integer>{12_i, 12_i, 12_i, 12_i}};
        case 4:
            // 12 items / 4 bins variable-load, wider cap.
            return Instance{"i4_12_4bins_load_wide", {1_i, 2_i, 3_i, 4_i, 5_i, 2_i, 3_i, 4_i, 1_i, 2_i, 5_i, 3_i}, items(12, 3),
                vector<std::pair<Integer, Integer>>{{6_i, 12_i}, {6_i, 12_i}, {6_i, 12_i}, {6_i, 12_i}}};
        case 5:
            // 8 items / 2 bins, tight cap, constant-cap.
            return Instance{"i5_8_2bins_tight_capa", {3_i, 5_i, 2_i, 4_i, 3_i, 4_i, 2_i, 5_i}, items(8, 1), vector<Integer>{14_i, 14_i}};
        case 6:
            // Wide-size constant-cap, exercises the DAG horizontally.
            return Instance{"i6_8_2bins_widesizes_capa", {1_i, 2_i, 4_i, 7_i, 1_i, 3_i, 5_i, 6_i}, items(8, 1), vector<Integer>{15_i, 15_i}};
        default: println(cerr, "unknown instance {}", n); std::exit(EXIT_FAILURE);
        }
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("BinPacking benchmark harness");
    cxxopts::ParseResult vars;

    try {
        options.add_options("Program options")                                    //
            ("help", "Display help information")                                  //
            ("instance", "Curated instance number (1..6)", cxxopts::value<int>()) //
            ("bounds-only", "Force bounds-only (skip Stage 3 DAG sweep)")         //
            ("upfront", "Use the opt-in upfront Stage 3 proof scaffolding")       //
            ("prove", "Generate a proof")                                         //
            ("proof-files-basename", "Basename for .opb and .pbp files",          //
                cxxopts::value<string>()->default_value("bin_packing_bench"))     //
            ("root-only", "Abort after the first complete propagation");
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
    bool bounds_only = vars.contains("bounds-only");
    bool upfront = vars.contains("upfront");
    auto level = bounds_only ? BinPackingConsistency{consistency::BC{}} : BinPackingConsistency{consistency::GAC{}};
    auto strategy = upfront ? BinPackingProofStrategy{proof_strategy::Upfront{}} : BinPackingProofStrategy{proof_strategy::PerCall{}};

    Problem p;
    vector<IntegerVariableID> items;
    items.reserve(inst.item_ranges.size());
    for (size_t i = 0; i < inst.item_ranges.size(); ++i)
        items.push_back(p.create_integer_variable(inst.item_ranges[i].first, inst.item_ranges[i].second, "item" + std::to_string(i)));

    if (std::holds_alternative<vector<std::pair<Integer, Integer>>>(inst.bins)) {
        const auto & loads_bounds = std::get<vector<std::pair<Integer, Integer>>>(inst.bins);
        vector<IntegerVariableID> loads;
        loads.reserve(loads_bounds.size());
        for (size_t b = 0; b < loads_bounds.size(); ++b)
            loads.push_back(p.create_integer_variable(loads_bounds[b].first, loads_bounds[b].second, "load" + std::to_string(b)));
        p.post(BinPacking{items, inst.sizes, loads} //
                .with_consistency(level)
                .with_proof_strategy(strategy));
    }
    else {
        const auto & caps = std::get<vector<Integer>>(inst.bins);
        p.post(BinPacking{items, inst.sizes, caps} //
                .with_consistency(level)
                .with_proof_strategy(strategy));
    }

    bool root_only = vars.contains("root-only");
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool { return true; },
            .trace = [&](const CurrentState &) -> bool { return ! root_only; },
            .branch = branch_with(variable_order::dom_then_deg(items), value_order::smallest_first())},
        vars.contains("prove") ? make_optional<ProofOptions>(vars["proof-files-basename"].as<string>()) : nullopt);

    print("{}", stats);
    return EXIT_SUCCESS;
}
