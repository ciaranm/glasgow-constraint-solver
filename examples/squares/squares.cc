/* Square packing: fit a collection of squares into a box without overlap.
 *
 * The benchmark the 2D cumulative relaxation exists for. `Disjunctive2D`'s
 * pairwise rule reasons about two rectangles at a time, so it is blind to the
 * statement that the squares crossing a given column are, between them, taller
 * than the box --- which is exactly what a square packing is made of, and what
 * Disjunctive2DRules::cumulative_relaxation derives. `--relaxation` turns it
 * on, so that both directions are measurable on the same model, and the proof
 * is the same size question one level up.
 *
 * The other Disjunctive2D example, shikaku, cannot answer that question: its
 * rectangles have *variable* sizes, and the relaxation sorts on a constant one.
 */

#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>

#include <cstdlib>
#include <iostream>
#include <map>
#include <optional>
#include <sstream>
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
using std::make_optional;
using std::map;
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
        vector<int> sizes;
        int width, height;
    };

    auto built_in_instances() -> map<string, Instance>
    {
        return {
            // Three squares of three in a box five wide: every pair overlaps in
            // x whatever it does, so all three must stack, and eight is a unit
            // short of the nine they need. The relaxation refutes it at the
            // root; without it the solver searches.
            {"tight", Instance{{3, 3, 3}, 5, 8}},
            // The same with the unit back, so it is satisfiable and the
            // refutation above is not a technicality.
            {"loose", Instance{{3, 3, 3}, 5, 9}},
            // Seven squares of two in a box five by five: 28 units of area in
            // 25. No square has a mandatory part on either axis at the root,
            // so time-tabling sees nothing until search makes some; the
            // overload check sees the area at once.
            {"area", Instance{{2, 2, 2, 2, 2, 2, 2}, 5, 5}},
            // Duijvestijn's order-21 perfect squared square: twenty-one
            // squares of distinct sizes that tile 112 x 112 exactly, the
            // smallest such dissection there is. Every column is exactly full,
            // so the relaxation is tight everywhere.
            //
            // The tiling is a published result, and *this solver does not
            // reproduce it*: neither arm closes it, and with --relaxation it
            // reached 24.7M search nodes and depth 13 of 42 in 23 minutes
            // without a packing. It is here as a benchmark rather than as a
            // demonstration, so always give it --timeout. What has been checked
            // here is only that the sizes' areas sum to 112^2 exactly.
            {"perfect21", Instance{{2, 4, 6, 7, 8, 9, 11, 15, 16, 17, 18, 19, 24, 25, 27, 29, 33, 35, 37, 42, 50}, 112, 112}},
        };
    }

    auto parse_sizes(const string & spec) -> vector<int>
    {
        vector<int> result;
        std::istringstream in{spec};
        string item;
        while (std::getline(in, item, ','))
            if (! item.empty())
                result.push_back(std::stoi(item));
        return result;
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Squares");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program options")                                                                   //
            ("help", "Display help information")                                                                 //
            ("prove", "Create a proof")                                                                          //
            ("proof-files-basename", "Basename for the .opb and .pbp files",                                     //
                cxxopts::value<string>()->default_value("squares"))                                              //
            ("stats", "Print solve statistics")                                                                  //
            ("relaxation", "Enable Disjunctive2D's cumulative relaxation rule")                                  //
            ("relaxation-overload", "Enable the overload check on the cumulative relaxation")                    //
            ("relaxation-edge-finding", "Enable edge-finding on the cumulative relaxation")                      //
            ("relaxation-ttef", "Enable time-table edge-finding on the cumulative relaxation")                   //
            ("all", "Enumerate every packing rather than stopping at the first")                                 //
            ("timeout", "Abort the solve after this many seconds", cxxopts::value<double>()->default_value("0")) //
            ("instance", "Built-in instance to solve", cxxopts::value<string>()->default_value("tight"))         //
            ("sizes", "Comma-separated square sizes, instead of a built-in instance", cxxopts::value<string>())  //
            ("width", "Box width, with --sizes", cxxopts::value<int>())                                          //
            ("height", "Box height, with --sizes", cxxopts::value<int>());                                       //

        options_vars = options.parse(argc, argv);
    }
    catch (const cxxopts::exceptions::exception & e) {
        println(cerr, "Error: {}", e.what());
        println(cerr, "Try {} --help", argv[0]);
        return EXIT_FAILURE;
    }

    if (options_vars.contains("help")) {
        println("Usage: {} [options]", argv[0]);
        println("");
        println("Pack squares of the given sizes into a box, without overlap. Non-overlap");
        println("is the diffn (Disjunctive2D) constraint; --relaxation adds the cumulative");
        println("relaxation, which is what sees that the squares crossing one column are");
        println("together taller than the box; --relaxation-overload adds the overload check");
        println("on that relaxation, which sees that the squares inside a range of columns");
        println("have more area between them than the box has there; and");
        println("--relaxation-edge-finding pushes a square away from a range of columns");
        println("that the squares inside it leave too little room in; --relaxation-ttef");
        println("does the same counting the mandatory parts of the squares outside it.");
        println("");
        println("Built-in instances: tight (unsatisfiable by one unit), loose, area (too");
        println("much area, with no mandatory parts at the root), perfect21");
        println("(Duijvestijn's order-21 squared square --- a benchmark, not a demo: this");
        println("solver does not close it, so always pass --timeout).");
        println("");
        print("{}", options.help());
        return EXIT_SUCCESS;
    }

    Instance inst;
    if (options_vars.contains("sizes")) {
        if (! options_vars.contains("width") || ! options_vars.contains("height")) {
            println(cerr, "Error: --sizes needs --width and --height too");
            return EXIT_FAILURE;
        }
        inst = Instance{parse_sizes(options_vars["sizes"].as<string>()), options_vars["width"].as<int>(), options_vars["height"].as<int>()};
    }
    else {
        auto instances = built_in_instances();
        auto name = options_vars["instance"].as<string>();
        if (! instances.contains(name)) {
            println(cerr, "Error: no built-in instance named '{}'", name);
            return EXIT_FAILURE;
        }
        inst = instances.at(name);
    }

    if (inst.sizes.empty()) {
        println(cerr, "Error: no squares to pack");
        return EXIT_FAILURE;
    }
    for (auto s : inst.sizes)
        if (s < 1 || s > inst.width || s > inst.height) {
            println(cerr, "Error: a square of {} does not fit in a {} x {} box", s, inst.width, inst.height);
            return EXIT_FAILURE;
        }

    Problem p;
    vector<IntegerVariableID> xs, ys, branch_vars;
    vector<Integer> sizes;
    for (auto s : inst.sizes) {
        xs.push_back(p.create_integer_variable(0_i, Integer{inst.width - s}, "x" + std::to_string(sizes.size())));
        ys.push_back(p.create_integer_variable(0_i, Integer{inst.height - s}, "y" + std::to_string(sizes.size())));
        sizes.push_back(Integer{s});
    }
    branch_vars = xs;
    branch_vars.insert(branch_vars.end(), ys.begin(), ys.end());

    Disjunctive2DRules rules{.cumulative_relaxation = options_vars.contains("relaxation"),
        .relaxation_overload = options_vars.contains("relaxation-overload"),
        .relaxation_edge_finding = options_vars.contains("relaxation-edge-finding"),
        .relaxation_time_table_edge_finding = options_vars.contains("relaxation-ttef")};
    p.post(Disjunctive2D{xs, ys, sizes, sizes}.with_rules(rules));

    auto enumerate = options_vars.contains("all");
    auto stats = gcs::bench::solve_with_timeout(options_vars["timeout"].as<double>(), p,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                           // One line per square: where its bottom-left corner went.
                           for (size_t k = 0; k < xs.size(); ++k)
                               println("{} at ({}, {})", inst.sizes[k], s(xs[k]).raw_value, s(ys[k]).raw_value);
                           println("");
                           return enumerate;
                       },
            .branch = branch_with(variable_order::dom_then_deg(branch_vars), value_order::smallest_first())},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    println("packings: {}", stats.solutions);
    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
