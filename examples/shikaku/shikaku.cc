#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/constraints/multiply.hh>
#include <gcs/presolvers/auto_table.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <optional>
#include <string>
#include <tuple>
#include <vector>

#include <cxxopts.hpp>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;

using std::cerr;
using std::ifstream;
using std::make_optional;
using std::map;
using std::nullopt;
using std::string;
using std::tuple;
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
    // A Shikaku instance: grid size and a list of clues (row, col, area).
    struct Instance
    {
        int width, height;
        vector<tuple<int, int, int>> clues; // (row, col, area)
    };

    // Built-in instances. Each is a genuine Shikaku: the clue areas sum to the
    // grid area, and the intended solution is unique.
    auto built_in_instances() -> map<string, Instance>
    {
        return {
            // A small 5x5 for CI / proof: tiles into five rectangles.
            {"small", Instance{5, 5, {{0, 0, 6}, {0, 3, 4}, {2, 0, 6}, {2, 2, 6}, {4, 2, 3}}}},
            // A "typical human" 7x7 (areas sum to 49), unique solution.
            {"human", Instance{7, 7, {{0, 0, 3}, {0, 1, 6}, {0, 4, 6}, {2, 1, 4}, {2, 3, 4}, {3, 0, 4}, {3, 3, 8}, {4, 1, 6}, {5, 3, 4}, {5, 5, 4}}}},
        };
    }

    auto read_instance(const string & path) -> Instance
    {
        ifstream in{path};
        if (! in)
            throw std::runtime_error{"could not open instance file " + path};
        int w, h;
        in >> w >> h;
        Instance inst{w, h, {}};
        for (int r = 0; r < h; ++r)
            for (int c = 0; c < w; ++c) {
                string tok;
                in >> tok;
                if (tok != ".") {
                    auto area = std::stoi(tok);
                    inst.clues.emplace_back(r, c, area);
                }
            }
        return inst;
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("Shikaku");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program options")                                                //
            ("help", "Display help information")                                              //
            ("prove", "Create a proof")                                                       //
            ("proof-files-basename", "Basename for the .opb and .pbp files",                  //
                cxxopts::value<string>()->default_value("shikaku"))                           //
            ("stats", "Print solve statistics")                                               //
            ("autotable", "Tabulate each rectangle's width/height during solving (stronger)") //
            ("instance", "Built-in instance to solve (small, human)",                         //
                cxxopts::value<string>()->default_value("small"))                             //
            ("file", "Read an instance from a file (W H then a grid of numbers and '.')",     //
                cxxopts::value<string>());                                                    //

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
        println("Shikaku: divide the grid into rectangles, one per clue, each of");
        println("area equal to its clue. Enumerates every solution (so a single");
        println("solution proves the puzzle is well-posed). Each rectangle is a");
        println("variable-origin, variable-size box; non-overlap is the diffn");
        println("(Disjunctive2D) constraint and the area is a (deliberately weak)");
        println("bounds-consistent multiplication -- --autotable strengthens it.");
        println("");
        print("{}", options.help());
        return EXIT_SUCCESS;
    }

    auto instances = built_in_instances();
    Instance inst = options_vars.contains("file") ? read_instance(options_vars["file"].as<string>()) : [&]() {
        auto name = options_vars["instance"].as<string>();
        if (! instances.contains(name))
            throw std::runtime_error{"no built-in instance named " + name};
        return instances.at(name);
    }();

    auto W = inst.width, H = inst.height;

    // Coverage is implied by non-overlap + in-bounds + total area = grid area,
    // so the areas must sum to the number of cells for a well-posed puzzle.
    int total = 0;
    for (auto & [r, c, a] : inst.clues)
        total += a;
    if (total != W * H) {
        println(cerr, "Error: clue areas sum to {} but the grid has {} cells", total, W * H);
        return EXIT_FAILURE;
    }

    Problem p;

    // One rectangle [x, x+w) x [y, y+h) per clue.
    vector<SimpleIntegerVariableID> xs, ys, ws, hs;
    vector<IntegerVariableID> xs_id, ys_id, ws_id, hs_id, branch_vars;
    for (size_t k = 0; k < inst.clues.size(); ++k) {
        auto [r, c, a] = inst.clues[k];
        auto sfx = std::to_string(k);
        // The left/top edge cannot pass the clue, so x <= c and y <= r.
        auto x = p.create_integer_variable(0_i, Integer{c}, "x" + sfx);
        auto y = p.create_integer_variable(0_i, Integer{r}, "y" + sfx);
        auto w = p.create_integer_variable(1_i, Integer{W}, "w" + sfx);
        auto h = p.create_integer_variable(1_i, Integer{H}, "h" + sfx);
        auto area = p.create_integer_variable(Integer{a}, Integer{a}, "area" + sfx);

        // Area = clue, as a (deliberately weak) bounds-consistent product:
        // pinned to BC so that --autotable stays meaningful, since the Auto
        // default would tabulate to GAC at these domain sizes.
        p.post(Multiply{w, h, area} //
                .with_consistency(consistency::BC{}));
        // The rectangle covers the clue cell: x + w >= c + 1, y + h >= r + 1.
        p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * x + 1_i * w, Integer{c + 1}});
        p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * y + 1_i * h, Integer{r + 1}});
        // The rectangle stays inside the grid: x + w <= W, y + h <= H.
        p.post(LinearLessThanEqual{WeightedSum{} + 1_i * x + 1_i * w, Integer{W}});
        p.post(LinearLessThanEqual{WeightedSum{} + 1_i * y + 1_i * h, Integer{H}});

        if (options_vars.contains("autotable"))
            p.add_presolver(AutoTable{vector<IntegerVariableID>{w, h}});

        xs.push_back(x);
        ys.push_back(y);
        ws.push_back(w);
        hs.push_back(h);
        xs_id.push_back(x);
        ys_id.push_back(y);
        ws_id.push_back(w);
        hs_id.push_back(h);
        branch_vars.push_back(x);
        branch_vars.push_back(y);
        branch_vars.push_back(w);
        branch_vars.push_back(h);
    }

    // No two rectangles overlap (diffn). All sizes are >= 1, so strict.
    p.post(Disjunctive2D{xs_id, ys_id, ws_id, hs_id, true});

    auto n = inst.clues.size();
    auto stats = solve_with(p, //
        SolveCallbacks{        //
            .solution = [&](const CurrentState & s) -> bool {
                // Render the tiling: each cell shows a letter identifying the
                // rectangle (clue) that covers it, so adjacent equal-area
                // regions are still distinguishable.
                for (int r = 0; r < H; ++r) {
                    for (int cc = 0; cc < W; ++cc) {
                        char owner = '?';
                        for (size_t k = 0; k < n; ++k) {
                            auto xk = s(xs[k]).raw_value, yk = s(ys[k]).raw_value;
                            auto wk = s(ws[k]).raw_value, hk = s(hs[k]).raw_value;
                            if (xk <= cc && cc < xk + wk && yk <= r && r < yk + hk) {
                                owner = static_cast<char>((k < 26 ? 'A' : 'a' - 26) + k);
                                break;
                            }
                        }
                        print("{}", owner);
                    }
                    println("");
                }
                println("");
                return true; // keep going: enumerate every solution
            },
            .branch = branch_with(variable_order::dom_then_deg(branch_vars), value_order::smallest_first())},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    println("solutions: {}{}", stats.solutions, stats.solutions == 1 ? " (unique -- the puzzle is well-posed)" : "");
    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
