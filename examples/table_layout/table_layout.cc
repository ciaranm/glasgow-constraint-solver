// Table-layout example for the Glasgow Constraint Solver.
//
// A port of the MiniZinc Challenge 2023 `table-layout` model (TableLayout.mzn),
// which lays out a rows x cols table of cells inside a fixed pixel width and
// minimises the total height. Each cell may be rendered in one of several
// configurations; configuration l of cell (r, c) occupies width[r][c][l] by
// height[r][c][l] pixels. Every cell in a row shares that row's height, every
// cell in a column shares that column's width, the column widths must fit in
// the pixel budget, and the objective is the sum of the row heights:
//
//     cellwidth[r][c]  == width[r][c][config[r][c]]
//     cellheight[r][c] == height[r][c][config[r][c]]
//     rowheight[r] >= cellheight[r][c]
//     colwidth[c]  >= cellwidth[r][c]
//     sum(colwidth) <= pixelwidth
//     minimise sum(rowheight)
//
// The interesting part is the first pair. Two element constraints sharing one
// index variable are just a ternary relation on (config, cellwidth, cellheight)
// written the long way round, so the natural native encoding is one Table per
// cell, whose tuples are the cell's legal configurations. That is what
// --variant table posts, and it is the reason this model is here: it gives
// Table a realistic instance with a size knob (--rows, --cols, --maxconfig,
// --pixelwidth), rather than the ten-recursion toy in examples/tables.
//
// --variant element instead posts the two ElementConstantArray constraints, so
// it matches what the MiniZinc frontend actually flattens this model to
// (array_int_element, not table), and --variant auto-table posts those and then
// asks the AutoTable presolver to tabulate the same triple, so the two
// tabulation routes can be compared on one instance.
//
// Instances come either from --dzn, which reads the Challenge data files
// unchanged, or from the built-in random generator, which matches how those
// files are built (see table_layout_instance.hh, and note the negative padding
// convention in the width and height arrays: it marks a cell with fewer than
// maxconfig configurations, and must not become a legal tuple).

#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/constraints/table.hh>
#include <gcs/presolvers/auto_table.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>
#include <examples/table_layout/table_layout_instance.hh>

#include <cstdlib>
#include <exception>
#include <iostream>
#include <optional>
#include <string>
#include <string_view>
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
using std::cout;
using std::make_optional;
using std::move;
using std::nullopt;
using std::optional;
using std::string;
using std::string_view;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using table_layout::Instance;

namespace
{
    // How the per-cell (config, cellwidth, cellheight) relation is posted. The
    // three variants describe the same relation, so they must all give the same
    // optimum; they differ only in what the propagator and the proof look like.
    // Spelled Post* so that `using enum Variant` inside the switch below does
    // not shadow the constraint and presolver classes of the same names.
    enum struct Variant
    {
        PostTable,     ///< One Table per cell, tuples listed explicitly.
        PostAutoTable, ///< The element pair, tabulated by the AutoTable presolver.
        PostElement    ///< The element pair alone, as MiniZinc flattens the model.
    };

    constexpr std::pair<string_view, Variant> variants[] = {
        {"table", Variant::PostTable},
        {"auto-table", Variant::PostAutoTable},
        {"element", Variant::PostElement},
    };

    auto find_variant(const string & name) -> optional<Variant>
    {
        for (const auto & [n, v] : variants)
            if (n == name)
                return v;
        return nullopt;
    }

    auto variant_names() -> string
    {
        string result;
        for (const auto & [n, _] : variants) {
            if (! result.empty())
                result += ", ";
            result += n;
        }
        return result;
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("table_layout");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program")                                            //
            ("help", "Display help information")                                  //
            ("prove", "Create a proof")                                           //
            ("proof-files-basename", "Basename for the .opb and .pbp files",      //
                cxxopts::value<string>()->default_value("table_layout"))          //
            ("stats", "Print full solve statistics")                              //
            ("timeout", "Abort the solve after this many seconds (0 = no limit)", //
                cxxopts::value<double>()->default_value("0"))                     //
            ;

        options.add_options("Model")                                                       //
            ("variant",                                                                    //
                "How to post the per-cell (config, width, height) relation. Supported: " + //
                    variant_names(),                                                       //
                cxxopts::value<string>()->default_value("table"))                          //
            ("branch",
                "Branching variable order: in-order, first-fail (default), dom-then-deg, or " //
                "dom-wdeg[:VARIANT]. first-fail matches the model's own search annotation.",  //
                cxxopts::value<string>()->default_value("first-fail"))                        //
            ;

        options.add_options("Instance")                                                                             //
            ("size", "Generate a --size by --size grid of cells (shorthand for --rows and --cols)",                 //
                cxxopts::value<int>()->default_value("4"))                                                          //
            ("rows", "Number of rows of cells (overrides --size)", cxxopts::value<int>())                           //
            ("cols", "Number of columns of cells (overrides --size)", cxxopts::value<int>())                        //
            ("maxconfig", "Largest number of configurations any cell may have",                                     //
                cxxopts::value<int>()->default_value("3"))                                                          //
            ("max-cell-size", "Cell widths and heights are drawn from 1 .. this",                                   //
                cxxopts::value<long>()->default_value("100"))                                                       //
            ("pixelwidth", "Budget for the sum of the column widths (0 = cols * max-cell-size)",                    //
                cxxopts::value<long>()->default_value("0"))                                                         //
            ("seed", "Seed for the random width and height arrays", cxxopts::value<unsigned>()->default_value("0")) //
            ("dzn", "Read a TableLayout.mzn .dzn data file instead of generating an instance",                      //
                cxxopts::value<string>())                                                                           //
            ;

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
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    auto variant_name = options_vars["variant"].as<string>();
    auto variant = find_variant(variant_name);
    if (! variant) {
        println(cerr, "Error: unknown --variant '{}'. Supported: {}.", variant_name, variant_names());
        return EXIT_FAILURE;
    }

    Instance instance;
    table_layout::Extents extents;
    try {
        if (options_vars.contains("dzn"))
            instance = table_layout::read_dzn(options_vars["dzn"].as<string>());
        else {
            auto size = options_vars["size"].as<int>();
            instance = table_layout::make_random(                                           //
                options_vars.contains("rows") ? options_vars["rows"].as<int>() : size,      //
                options_vars.contains("cols") ? options_vars["cols"].as<int>() : size,      //
                options_vars["maxconfig"].as<int>(), options_vars["pixelwidth"].as<long>(), //
                options_vars["max-cell-size"].as<long>(), options_vars["seed"].as<unsigned>());
        }
        extents = table_layout::extents(instance);
    }
    catch (const std::exception & e) {
        println(cerr, "Error building instance: {}", e.what());
        return EXIT_FAILURE;
    }

    Problem problem;

    // Following the MiniZinc model exactly: config is 1 .. maxconfig even for a
    // cell with fewer configurations (the relation prunes the surplus values),
    // and every width and height variable shares one pair of global bounds.
    auto min_width = Integer{extents.min_width}, max_width = Integer{extents.max_width};
    auto min_height = Integer{extents.min_height}, max_height = Integer{extents.max_height};

    vector<vector<IntegerVariableID>> config, cellwidth, cellheight;
    for (int r = 0; r < instance.rows; ++r) {
        config.push_back(problem.create_integer_variable_vector(instance.cols, 1_i, Integer{instance.maxconfig}, "config" + std::to_string(r + 1)));
        cellwidth.push_back(problem.create_integer_variable_vector(instance.cols, min_width, max_width, "cellwidth" + std::to_string(r + 1)));
        cellheight.push_back(problem.create_integer_variable_vector(instance.cols, min_height, max_height, "cellheight" + std::to_string(r + 1)));
    }

    auto rowheight = problem.create_integer_variable_vector(instance.rows, min_height, max_height, "rowheight");
    auto colwidth = problem.create_integer_variable_vector(instance.cols, min_width, max_width, "colwidth");
    auto totalheight = problem.create_integer_variable(min_height, Integer{instance.rows} * max_height, "totalheight");

    for (int r = 0; r < instance.rows; ++r)
        for (int c = 0; c < instance.cols; ++c) {
            auto configs = table_layout::legal_configurations(instance, r, c);

            switch (*variant) {
                using enum Variant;
            case PostTable: {
                SimpleTuples tuples;
                for (const auto & [l, w, h] : configs)
                    tuples.push_back({Integer{l}, Integer{w}, Integer{h}});
                problem.post(Table{{config[r][c], cellwidth[r][c], cellheight[r][c]}, move(tuples)});
            } break;

            case PostAutoTable:
            case PostElement: {
                // The padding entries stay in the arrays: they are outside the
                // cellwidth / cellheight domains, so they are unselectable, which
                // is how the MiniZinc model excludes them too.
                vector<Integer> widths, heights;
                for (int l = 0; l < instance.maxconfig; ++l) {
                    widths.push_back(Integer{instance.width[r][c][l]});
                    heights.push_back(Integer{instance.height[r][c][l]});
                }
                problem.post(ElementConstantArray{cellwidth[r][c], {config[r][c], 1_i}, move(widths)});
                problem.post(ElementConstantArray{cellheight[r][c], {config[r][c], 1_i}, move(heights)});
                if (*variant == PostAutoTable)
                    problem.add_presolver(AutoTable{{config[r][c], cellwidth[r][c], cellheight[r][c]}});
            } break;
            }

            problem.post(LessThanEqual{cellheight[r][c], rowheight[r]});
            problem.post(LessThanEqual{cellwidth[r][c], colwidth[c]});
        }

    WeightedSum width_sum;
    for (const auto & v : colwidth)
        width_sum += 1_i * v;
    problem.post(LinearLessThanEqual{move(width_sum), Integer{instance.pixelwidth}});

    WeightedSum height_sum;
    for (const auto & v : rowheight)
        height_sum += 1_i * v;
    height_sum += -1_i * totalheight;
    problem.post(LinearEquality{move(height_sum), 0_i});

    problem.minimise(totalheight);

    // The model's own annotation is first_fail / indomain_min over the config
    // variables only, so mirror that and then fall back to everything else (the
    // row heights, column widths and the objective are all determined once the
    // configurations are, but they still have to be fixed to have a solution).
    vector<IntegerVariableID> decisions, everything;
    for (int r = 0; r < instance.rows; ++r)
        for (int c = 0; c < instance.cols; ++c)
            decisions.push_back(config[r][c]);
    everything = decisions;
    for (const auto & v : colwidth)
        everything.push_back(v);
    for (const auto & v : rowheight)
        everything.push_back(v);
    everything.push_back(totalheight);
    for (int r = 0; r < instance.rows; ++r)
        for (int c = 0; c < instance.cols; ++c) {
            everything.push_back(cellwidth[r][c]);
            everything.push_back(cellheight[r][c]);
        }

    auto branch_spec = options_vars["branch"].as<string>();
    optional<BranchHeuristic> decision_brancher;
    if (branch_spec == "first-fail")
        decision_brancher = branch_with(variable_order::dom(decisions), value_order::smallest_in());
    else if (branch_spec == "in-order")
        decision_brancher = branch_with(variable_order::in_order(decisions), value_order::smallest_in());
    else if (branch_spec == "dom-then-deg")
        decision_brancher = branch_with(variable_order::dom_then_deg(decisions), value_order::smallest_in());
    else if (branch_spec == "dom-wdeg")
        decision_brancher = branch_with(variable_order::dom_wdeg(decisions), value_order::smallest_in());
    else if (branch_spec.starts_with("dom-wdeg:")) {
        auto scheme = bench::scheme_from_string(branch_spec.substr(branch_spec.find(':') + 1));
        if (! scheme) {
            println(cerr, "Error: unknown dom-wdeg weighting scheme in '{}'.", branch_spec);
            return EXIT_FAILURE;
        }
        decision_brancher = branch_with(variable_order::dom_wdeg(decisions, *scheme), value_order::smallest_in());
    }
    else {
        println(cerr, "Error: unknown --branch value '{}'.", branch_spec);
        return EXIT_FAILURE;
    }

    auto brancher = branch_sequence(*decision_brancher, branch_with(variable_order::dom_then_deg(everything), value_order::smallest_first()));

    optional<Integer> best_height;
    vector<Integer> best_rowheights;
    bool proven = false;

    auto stats = bench::solve_with_timeout(options_vars["timeout"].as<double>(), problem,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                           best_height = s(totalheight);
                           best_rowheights.clear();
                           for (const auto & v : rowheight)
                               best_rowheights.push_back(s(v));
                           return true;
                       },
            .branch = brancher,
            .completed = [&]() { proven = true; }},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    string status;
    if (proven)
        status = best_height ? "optimal" : "infeasible";
    else
        status = best_height ? "timeout" : "timeout-nosolution";

    println("instance: {}", instance.description);
    println("variant: {}", variant_name);
    println("status: {}", status);
    if (best_height) {
        println("totalheight: {}", best_height->raw_value);
        print("rowheight:");
        for (const auto & v : best_rowheights)
            print(" {}", v.raw_value);
        println("");
    }
    else
        println("totalheight: none");
    println("recursions: {}", stats.recursions);
    println("propagations: {}", stats.propagations);
    println("wall_time_s: {:.6f}", static_cast<double>(stats.solve_time.count()) / 1.0e6);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
