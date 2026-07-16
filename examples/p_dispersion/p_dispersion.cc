// p-dispersion example for the Glasgow Constraint Solver.
//
// Chooses p of n candidate sites so that the closest selected pair is as far
// apart as possible (maximise z = min_{i<j} D[x_i][x_j]), following the indexed
// model of Lagerkvist, "Propagation Algorithms for the Minimum-Distance
// Constraint over Selected Points" (ModRef 2026), Section 3. The constraint
// linking the selected points to z is posted via one of several variants,
// selected with --variant. Phase 1 implements the "tuple" decomposition: one
// auxiliary distance variable y_ij = D[x_i][x_j] per selected-position pair
// (posted with Element2DConstantArray), together with z = min_{i<j} y_ij
// (ArrayMin). Optional pairwise lower-bound requirements r_ij (the p-dispersion
// with distance constraints, "PDDP", variant) are posted as y_ij >= r_ij + 1.
//
// Later phases add more variants (a dedicated min_distance constraint and its
// propagators) to this same binary; the --variant dispatch below is the seam.

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>
#include <examples/p_dispersion/p_dispersion_instance.hh>

#include <cstdlib>
#include <iostream>
#include <memory>
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
using std::make_shared;
using std::nullopt;
using std::optional;
using std::string;
using std::to_string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using p_dispersion::Instance;

namespace
{
    using DistanceMatrix = vector<vector<Integer>>;

    // Post the "tuple" decomposition of the minimum-distance relation:
    //   y_ij = D[x_i][x_j]                       (Element2DConstantArray)
    //   y_ij >= r_ij + 1   when a requirement r_ij is given (PDDP)
    //   z = min_{i<j} y_ij                        (ArrayMin)
    // reqs, when non-empty, is the raw r_ij matrix (p x p, upper triangular
    // used); reqs[i][j] < 0 means "no requirement for this pair".
    auto post_tuple_variant(Problem & problem, const vector<IntegerVariableID> & x, IntegerVariableID z,
        const std::shared_ptr<const DistanceMatrix> & distance, const vector<vector<long>> & reqs, Integer max_dist) -> void
    {
        auto pp = static_cast<int>(x.size());
        vector<IntegerVariableID> ys;
        for (int i = 0; i < pp; ++i)
            for (int j = i + 1; j < pp; ++j) {
                auto y = problem.create_integer_variable(0_i, max_dist, "y_" + to_string(i) + "_" + to_string(j));
                problem.post(Element2DConstantArray{y, x[i], x[j], distance});
                if (! reqs.empty() && reqs[i][j] >= 0)
                    problem.post(GreaterThanEqual{y, constant_variable(Integer{reqs[i][j] + 1})});
                ys.push_back(y);
            }
        problem.post(ArrayMin{ys, z});
    }

    // Parse "WxH" (or a single "N" meaning N x N) into a (width, height) pair.
    auto parse_grid_spec(const string & spec) -> std::pair<int, int>
    {
        auto x_pos = spec.find_first_of("xX");
        if (x_pos == string::npos) {
            auto n = std::stoi(spec);
            return {n, n};
        }
        auto w = std::stoi(spec.substr(0, x_pos));
        auto h = std::stoi(spec.substr(x_pos + 1));
        return {w, h};
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("p-dispersion");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program")                                            //
            ("help", "Display help information")                                  //
            ("prove", "Create a proof")                                           //
            ("proof-files-basename", "Basename for the .opb and .pbp files",      //
                cxxopts::value<string>()->default_value("p_dispersion"))          //
            ("stats", "Print full solve statistics")                              //
            ("timeout", "Abort the solve after this many seconds (0 = no limit)", //
                cxxopts::value<double>()->default_value("0"))                     //
            ;

        options.add_options("Model")                                                                    //
            ("variant", "Constraint variant to post (currently only: tuple)",                           //
                cxxopts::value<string>()->default_value("tuple"))                                       //
            ("p,points", "Number of sites to select (>= 2)", cxxopts::value<int>()->default_value("3")) //
            ("initial-lb",
                "Initial lower bound on z. Default 1 forbids coincident sites "                           //
                "(positive separation); use 0 to allow duplicate sites (z can be 0).",                    //
                cxxopts::value<long long>()->default_value("1"))                                          //
            ("all-different", "Also post the (redundant) AllDifferent over the selected-point variables") //
            ("homogeneous-req",
                "Post a homogeneous PDDP requirement r_ij = R for every position pair "                     //
                "(model enforces D >= R + 1). Overridden by file-provided per-pair reqs.",                  //
                cxxopts::value<long>())                                                                     //
            ("branch", "Branching variable order: in-order (default), dom-then-deg, or dom-wdeg[:VARIANT]", //
                cxxopts::value<string>()->default_value("in-order"))                                        //
            ;

        options.add_options("Instance") //
            ("grid",
                "Candidate sites are the points of a WxH integer grid (e.g. 10x10, or N for NxN), "  //
                "rounded Euclidean distances",                                                       //
                cxxopts::value<string>())                                                            //
            ("random-euclidean", "Candidate sites are N random points, rounded Euclidean distances", //
                cxxopts::value<int>())                                                               //
            ("seed", "Seed for --random-euclidean", cxxopts::value<unsigned>()->default_value("0"))  //
            ("span", "Coordinate range [0, span] for --random-euclidean",                            //
                cxxopts::value<long>()->default_value("1000"))                                       //
            ("file", "Read an MDPLIB-style distance instance from PATH", cxxopts::value<string>())   //
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

    auto variant = options_vars["variant"].as<string>();
    if (variant != "tuple") {
        println(cerr, "Error: unknown --variant '{}'. Phase 1 supports only 'tuple'.", variant);
        return EXIT_FAILURE;
    }

    // Build the instance from exactly one source; default to a small grid so a
    // bare run (as used by the proof-verification test) does something valid.
    Instance instance;
    try {
        int sources = static_cast<int>(options_vars.contains("grid")) + static_cast<int>(options_vars.contains("random-euclidean")) +
            static_cast<int>(options_vars.contains("file"));
        if (sources > 1) {
            println(cerr, "Error: choose at most one of --grid, --random-euclidean, --file.");
            return EXIT_FAILURE;
        }
        if (options_vars.contains("grid")) {
            auto [w, h] = parse_grid_spec(options_vars["grid"].as<string>());
            instance = p_dispersion::make_grid(w, h);
        }
        else if (options_vars.contains("random-euclidean")) {
            instance = p_dispersion::make_random_euclidean(
                options_vars["random-euclidean"].as<int>(), options_vars["seed"].as<unsigned>(), options_vars["span"].as<long>());
        }
        else if (options_vars.contains("file")) {
            instance = p_dispersion::read_file(options_vars["file"].as<string>());
        }
        else {
            instance = p_dispersion::make_grid(3, 3);
        }
    }
    catch (const std::exception & e) {
        println(cerr, "Error building instance: {}", e.what());
        return EXIT_FAILURE;
    }

    // Number of positions: the instance file may fix it, otherwise --points.
    int pp = instance.p.value_or(options_vars["points"].as<int>());
    if (instance.p && options_vars.count("points") && options_vars["points"].as<int>() != *instance.p)
        println(cerr, "Note: instance fixes p = {}, ignoring --points {}", *instance.p, options_vars["points"].as<int>());

    if (pp < 2) {
        println(cerr, "Error: p must be at least 2 (got {}).", pp);
        return EXIT_FAILURE;
    }
    if (pp > instance.n) {
        println(cerr, "Error: p = {} exceeds the number of candidate sites n = {}.", pp, instance.n);
        return EXIT_FAILURE;
    }

    auto max_dist = p_dispersion::max_distance(instance);
    auto initial_lb = Integer{options_vars["initial-lb"].as<long long>()};
    if (initial_lb < 0_i) {
        println(cerr, "Error: --initial-lb must be non-negative.");
        return EXIT_FAILURE;
    }
    if (initial_lb > max_dist) {
        println(cerr, "Error: --initial-lb {} exceeds the largest distance {} (instance is trivially infeasible).", initial_lb.raw_value,
            max_dist.raw_value);
        return EXIT_FAILURE;
    }

    // Requirements r_ij: file-provided per-pair reqs take priority; otherwise a
    // homogeneous value if requested; otherwise none (plain p-dispersion).
    vector<vector<long>> reqs;
    if (! instance.reqs.empty()) {
        if (static_cast<int>(instance.reqs.size()) < pp)
            println(cerr, "Warning: instance provides fewer requirement rows than p; missing pairs are unconstrained.");
        reqs = instance.reqs;
    }
    else if (options_vars.contains("homogeneous-req")) {
        reqs.assign(pp, vector<long>(pp, options_vars["homogeneous-req"].as<long>()));
    }

    Problem problem;
    auto x = problem.create_integer_variable_vector(pp, 0_i, Integer{instance.n - 1}, "x");
    auto z = problem.create_integer_variable(initial_lb, max_dist, "z");

    auto distance = make_shared<const DistanceMatrix>(instance.distance);
    post_tuple_variant(problem, x, z, distance, reqs, max_dist);

    if (options_vars.contains("all-different"))
        problem.post(AllDifferent{x});

    problem.maximise(z);

    // Branch over all selected-point variables and then z (z last, ascending),
    // per the paper. z is functionally determined by x here, so it is only in
    // the branch list to guarantee it is fixed when the solution is read.
    vector<IntegerVariableID> branch_vars = x;
    branch_vars.push_back(z);

    auto branch_spec = options_vars["branch"].as<string>();
    optional<BranchHeuristic> brancher;
    if (branch_spec == "in-order")
        brancher = branch_with(variable_order::in_order(branch_vars), value_order::smallest_first());
    else if (branch_spec == "dom-then-deg")
        brancher = branch_with(variable_order::dom_then_deg(branch_vars), value_order::smallest_first());
    else if (branch_spec == "dom-wdeg")
        brancher = branch_with(variable_order::dom_wdeg(branch_vars), value_order::smallest_first());
    else if (branch_spec.starts_with("dom-wdeg:")) {
        auto scheme = bench::scheme_from_string(branch_spec.substr(branch_spec.find(':') + 1));
        if (! scheme) {
            println(cerr, "Error: unknown dom-wdeg weighting scheme in '{}'.", branch_spec);
            return EXIT_FAILURE;
        }
        brancher = branch_with(variable_order::dom_wdeg(branch_vars, *scheme), value_order::smallest_first());
    }
    else {
        println(cerr, "Error: unknown --branch value '{}'.", branch_spec);
        return EXIT_FAILURE;
    }

    optional<Integer> best_z;
    vector<Integer> best_sites;
    bool proven = false;

    auto stats = bench::solve_with_timeout(options_vars["timeout"].as<double>(), problem,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                           best_z = s(z);
                           best_sites.clear();
                           for (const auto & v : x)
                               best_sites.push_back(s(v));
                           return true;
                       },
            .branch = *brancher,
            .completed = [&]() { proven = true; }},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    string status;
    if (proven)
        status = best_z ? "optimal" : "infeasible";
    else
        status = best_z ? "timeout" : "timeout-nosolution";

    auto wall_time_s = static_cast<double>(stats.solve_time.count()) / 1.0e6;

    println("instance: {}", instance.description);
    println("n: {}", instance.n);
    println("p: {}", pp);
    println("variant: {}", variant);
    println("status: {}", status);
    if (best_z) {
        println("best_z: {}", best_z->raw_value);
        print("sites:");
        for (const auto & v : best_sites)
            print(" {}", v.raw_value);
        println("");
    }
    else
        println("best_z: none");
    println("recursions: {}", stats.recursions);
    println("propagations: {}", stats.propagations);
    println("wall_time_s: {:.6f}", wall_time_s);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
