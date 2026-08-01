// Difference-chain example for the Glasgow Constraint Solver.
//
// Builds Example 8 of Kletzander, Dekker, Schutt and Stuckey, "Global
// Difference Constraint Propagation for Constraint Programming"
// (arXiv:2607.20022), Section 4.2: a system of difference constraints
//
//     y_{i-1} - y_i <= 0        2 <= i <= n
//     y_0     - y_i <= i - 1    1 <= i <= n
//     y_n     - x_0 <= 0
//     x_i     - x_j <= 0        0 <= i < j <= n
//
// over y_0..y_n, x_0..x_n, all with domain [0 .. k*n]. That domain is a
// fixpoint, and none of the constraints is implied by it, so nothing can be
// retired from the propagation queue. Raising the lower bound of y_0 to n then
// costs Theta(n^3) work under a one-propagator-per-constraint engine with a
// FIFO queue -- the domain of x_0 changes n times, and each constraint is
// queued n times -- where a global difference-logic propagator reaches the same
// fixpoint in Theta(n^2), visiting each edge once. This program is the
// instrumented version of that pathology: it reports propagations and time to
// reach the root fixpoint, so the asymptotics can be measured rather than
// asserted.
//
// The cubic blow-up is contingent on the order the constraints are posted in,
// which is why --order is a first-class option and every measurement taken with
// this program has to say which order it used. Posting the long jumps first, in
// descending i (so y_0 - y_n <= n-1 fires first), reproduces the paper's bad
// case; posting the unit chain first and then the jumps in ascending i is
// Theta(n^2) and shows nothing. The former is --order=unlucky, the default.
//
// --mode=refute adds one further difference constraint, x_n - y_0 <= -1, which
// closes a negative cycle of weight -1 around the whole chain
// y_0 <= y_1 <= ... <= y_n <= x_0 <= x_1 <= ... <= x_n. The system is then
// unsatisfiable, but not locally so: no individual constraint is violated by
// the initial domains, and per-constraint bounds propagation can only discover
// it by crawling every bound up one unit at a time, so both the work and the
// emitted proof grow with the domain size (that is, with k). A global
// propagator refutes an n-edge negative cycle by summing the edges around it,
// which is a single cutting-planes step whatever the domains are; this mode is
// the baseline that claim will be measured against.
//
// --variant=decomposed posts every constraint as its own two-term
// LinearLessThanEqual, i.e. 1*a + -1*b <= d, which is the shape the presolver
// planned in issue #571 will detect. Deliberately not LessThanEqual/Comparison
// over an offset view: those are emitted unlabelled in the OPB, so a global
// propagator could not cite them in a proof.
//
// --variant=global posts exactly the same edges, in exactly the same order, as
// a single DifferenceConstraints. That runs one Bellman-Ford pass over the
// whole graph per wake instead of one propagator per edge, so the fixpoint cost
// stops depending on the order the edges were given in; and in --mode=refute it
// refutes the negative cycle by summing the cycle's edge rows, which is one
// cutting-planes step whatever the domains are.
//
// --variant=presolved posts the decomposed model and then adds the
// DifferenceLogic presolver, which detects those two-term linears and installs
// the same global propagator over them without the model being rewritten. The
// donors' own propagators stay installed (the paper's section 4.4 hybrid), which
// is what makes this the interesting middle column: it answers whether the
// presolver route recovers the global route's win while still paying for the
// redundant propagators, and whether the presolver's propagator running last in
// registration order (gcs has no propagator priorities, see issue #582) costs
// anything measurable. --disable-donors additionally retires the lifted donors'
// propagators, which is the same experiment with that cost removed.

#include <gcs/constraints/difference.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/presolvers/difference_logic.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>

#include <cstdlib>
#include <iostream>
#include <memory>
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
#include <fmt/ranges.h>
#endif

using namespace gcs;

using std::cerr;
using std::cout;
using std::make_optional;
using std::make_shared;
using std::nullopt;
using std::optional;
using std::shared_ptr;
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

namespace
{
    enum struct Order
    {
        Unlucky,
        Lucky
    };

    enum struct Mode
    {
        Fixpoint,
        Refute
    };

    enum struct Variant
    {
        Decomposed,
        Presolved,
        Global
    };

    // Build Example 8's constraints over y and x. The two orders contain
    // exactly the same edges and differ only in the sequence they come out in,
    // which is what seeds the propagation queue for --variant=decomposed (and
    // which --variant=global is designed not to care about).
    auto example_8_edges(const vector<IntegerVariableID> & y, const vector<IntegerVariableID> & x, int n, Order order) -> vector<DifferenceEdge>
    {
        vector<DifferenceEdge> edges;

        auto edge = [&](IntegerVariableID a, IntegerVariableID b, Integer d) { edges.push_back(DifferenceEdge{a, b, d}); };

        auto chain_ascending = [&] {
            for (int i = 2; i <= n; ++i)
                edge(y[i - 1], y[i], 0_i);
        };
        auto chain_descending = [&] {
            for (int i = n; i >= 2; --i)
                edge(y[i - 1], y[i], 0_i);
        };
        auto jumps_ascending = [&] {
            for (int i = 1; i <= n; ++i)
                edge(y[0], y[i], Integer{i - 1});
        };
        auto jumps_descending = [&] {
            for (int i = n; i >= 1; --i)
                edge(y[0], y[i], Integer{i - 1});
        };
        auto bridge = [&] { edge(y[n], x[0], 0_i); };
        auto x_pairs = [&] {
            for (int i = 0; i <= n; ++i)
                for (int j = i + 1; j <= n; ++j)
                    edge(x[i], x[j], 0_i);
        };

        switch (order) {
            using enum Order;
        case Unlucky:
            // The paper's bad case: the long jump y_0 - y_n <= n-1 is the first
            // thing to fire once y_0's lower bound moves, so every y_i is raised
            // from the far end and the unit chain then has to walk each of them
            // up again, one unit per pass.
            jumps_descending();
            bridge();
            chain_descending();
            x_pairs();
            break;
        case Lucky:
            // The unit chain first, then the jumps in ascending i: bounds reach
            // their fixpoint in one sweep.
            chain_ascending();
            jumps_ascending();
            bridge();
            x_pairs();
            break;
        }

        return edges;
    }

    // Hand the same edges to the solver, either one propagator each or all at
    // once. Both variants produce the same OPB rows for the same edges (one
    // labelled inequality per edge), so the proofs are directly comparable.
    auto post_edges(Problem & problem, const vector<DifferenceEdge> & edges, Variant variant, bool disable_donors,
        const shared_ptr<DifferenceLogicStats> & presolver_stats) -> void
    {
        switch (variant) {
            using enum Variant;
        case Presolved:
        case Decomposed:
            for (const auto & e : edges)
                problem.post(LinearLessThanEqual{WeightedSum{} + 1_i * e.x + -1_i * e.y, e.d});
            if (variant == Presolved)
                problem.add_presolver(DifferenceLogic{presolver_stats}.disabling_lifted_donors(disable_donors));
            break;
        case Global: problem.post(DifferenceConstraints{edges}); break;
        }
    }

    // The --variant names, in help order.
    constexpr string_view variants[] = {"decomposed", "presolved", "global"};

    auto variant_names() -> string
    {
        string result;
        for (const auto & v : variants) {
            if (! result.empty())
                result += ", ";
            result += v;
        }
        return result;
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("difference_chain");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program")                                            //
            ("help", "Display help information")                                  //
            ("prove", "Create a proof")                                           //
            ("proof-files-basename", "Basename for the .opb and .pbp files",      //
                cxxopts::value<string>()->default_value("difference_chain"))      //
            ("stats", "Print full solve statistics")                              //
            ("timeout", "Abort the solve after this many seconds (0 = no limit)", //
                cxxopts::value<double>()->default_value("0"))                     //
            ;

        // The paper's parameters are n and k. cxxopts cannot register a long
        // option of one character (its --option regex demands two or more), so
        // each gets a descriptive long name and the paper's letter as a short
        // one: -n 40 and --size=40 are the same thing.
        options.add_options("Model")                                                                     //
            ("n,size", "Size parameter n: the system has 2n + 2 variables and n(n+5)/2 + 1 constraints", //
                cxxopts::value<int>()->default_value("20"))                                              //
            ("k,domain-multiplier", "Domain multiplier k: every variable has domain [0 .. k*n]",         //
                cxxopts::value<int>()->default_value("2"))                                               //
            ("order",                                                                                    //
                "Order to post the constraints in: unlucky (the paper's bad case, long jumps first in "  //
                "descending i, then the unit chain) or lucky (unit chain first, then ascending jumps)",  //
                cxxopts::value<string>()->default_value("unlucky"))                                      //
            ("mode",                                                                                     //
                "fixpoint (post y_0 >= n and chase the resulting fixpoint, satisfiable) or refute "      //
                "(also post x_n - y_0 <= -1, closing a negative cycle, unsatisfiable)",                  //
                cxxopts::value<string>()->default_value("fixpoint"))                                     //
            ("variant", "Model variant to post. Supported: " + variant_names(),                          //
                cxxopts::value<string>()->default_value("decomposed"))                                   //
            ("disable-donors",                                                                           //
                "With --variant=presolved, also retire the lifted constraints' own propagators, so "     //
                "only the global one runs over them")                                                    //
            ("all", "Find all solutions rather than stopping at the first")                              //
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
        println("Example 8 of Kletzander, Dekker, Schutt and Stuckey, \"Global Difference");
        println("Constraint Propagation for Constraint Programming\": a system of difference");
        println("constraints whose fixpoint costs Theta(n^3) to reach with one propagator per");
        println("constraint, but only Theta(n^2) with a global difference-logic propagator.");
        println("");
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    auto n = options_vars["size"].as<int>();
    if (n < 1) {
        println(cerr, "Error: --size (-n) must be at least 1 (got {}).", n);
        return EXIT_FAILURE;
    }

    auto k = options_vars["domain-multiplier"].as<int>();
    if (k < 1) {
        println(cerr, "Error: --domain-multiplier (-k) must be at least 1 (got {}).", k);
        return EXIT_FAILURE;
    }

    auto order_name = options_vars["order"].as<string>();
    optional<Order> order;
    if (order_name == "unlucky")
        order = Order::Unlucky;
    else if (order_name == "lucky")
        order = Order::Lucky;
    else {
        println(cerr, "Error: unknown --order '{}'. Supported: unlucky, lucky.", order_name);
        return EXIT_FAILURE;
    }

    auto mode_name = options_vars["mode"].as<string>();
    optional<Mode> mode;
    if (mode_name == "fixpoint")
        mode = Mode::Fixpoint;
    else if (mode_name == "refute")
        mode = Mode::Refute;
    else {
        println(cerr, "Error: unknown --mode '{}'. Supported: fixpoint, refute.", mode_name);
        return EXIT_FAILURE;
    }

    auto variant_name_given = options_vars["variant"].as<string>();
    optional<Variant> variant;
    if (variant_name_given == "decomposed")
        variant = Variant::Decomposed;
    else if (variant_name_given == "presolved")
        variant = Variant::Presolved;
    else if (variant_name_given == "global")
        variant = Variant::Global;
    else {
        println(cerr, "Error: unknown --variant '{}'. Supported: {}.", variant_name_given, variant_names());
        return EXIT_FAILURE;
    }

    Problem problem;
    auto hi = Integer{static_cast<long long>(k) * n};
    auto y = problem.create_integer_variable_vector(n + 1, 0_i, hi, "y");
    auto x = problem.create_integer_variable_vector(n + 1, 0_i, hi, "x");

    auto edges = example_8_edges(y, x, n, *order);

    // One extra difference constraint closing a negative cycle of weight -1
    // around y_0 <= ... <= y_n <= x_0 <= ... <= x_n, which the chain makes
    // reachable at cost 0. Nothing about it is locally violated.
    if (*mode == Mode::Refute)
        edges.push_back(DifferenceEdge{x[n], y[0], -1_i});

    auto disable_donors = options_vars.contains("disable-donors");
    if (disable_donors && *variant != Variant::Presolved) {
        println(cerr, "Error: --disable-donors only means anything with --variant=presolved.");
        return EXIT_FAILURE;
    }

    auto presolver_stats = make_shared<DifferenceLogicStats>();
    post_edges(problem, edges, *variant, disable_donors, presolver_stats);

    // The lower-bound bump that starts the chase. Posted last, so that the
    // difference constraints are all in the queue ahead of it and the bump wakes
    // them exactly as the paper describes. Not a difference constraint, and
    // posted identically in both variants, so the comparison is between the two
    // ways of handling the edges and nothing else.
    problem.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * y[0], Integer{n}});

    auto all = options_vars.contains("all");
    bool proven = false;
    optional<vector<Integer>> first_solution;

    auto stats = bench::solve_with_timeout(options_vars["timeout"].as<double>(), problem,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                           if (! first_solution) {
                               first_solution = vector<Integer>{};
                               for (const auto & v : y)
                                   first_solution->push_back(s(v));
                               for (const auto & v : x)
                                   first_solution->push_back(s(v));
                           }
                           return all;
                       },
            .completed = [&]() { proven = true; }},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    string status;
    if (first_solution)
        status = proven ? "satisfiable-complete" : "satisfiable";
    else
        status = proven ? "unsatisfiable" : "timeout";

    auto wall_time_s = static_cast<double>(stats.solve_time.count()) / 1.0e6;

    println("n: {}", n);
    println("k: {}", k);
    println("order: {}", order_name);
    println("mode: {}", mode_name);
    println("variant: {}", variant_name_given);
    if (*variant == Variant::Presolved) {
        println("disable_donors: {}", disable_donors ? "yes" : "no");
        println("presolver_edges_lifted: {}", presolver_stats->edges_lifted);
        println("presolver_nodes: {}", presolver_stats->nodes);
        println("presolver_donors_disabled: {}", presolver_stats->donor_propagators_disabled);
    }
    println("all: {}", all ? "yes" : "no");
    println("domain: 0..{}", hi.raw_value);
    println("status: {}", status);
    if (first_solution) {
        print("first_solution:");
        for (const auto & v : *first_solution)
            print(" {}", v.raw_value);
        println("");
    }
    println("solutions: {}", stats.solutions);
    println("recursions: {}", stats.recursions);
    println("propagations: {}", stats.propagations);
    println("wall_time_s: {:.6f}", wall_time_s);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
