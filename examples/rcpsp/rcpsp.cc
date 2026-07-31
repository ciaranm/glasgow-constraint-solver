// Resource-constrained project scheduling (RCPSP) example for the Glasgow
// Constraint Solver.
//
// A project is a set of tasks, each with a duration and a demand on each of a
// number of renewable resources, together with precedences saying that one task
// must finish before another starts. Some of the tasks also need a single
// machine that can only do one thing at a time. The goal is to schedule every
// task so that no resource is ever oversubscribed, and the makespan -- the time
// at which the last task finishes -- is as small as possible.
//
// The model is the textbook one: an integer start-time variable per task, one
// Cumulative per renewable resource, one Disjunctive over the tasks that need
// the machine, and a LinearGreaterThanEqual per precedence. The shape follows
// the MiniZinc Challenge 2024 aircraft-disassembly model, which posts two
// cumulative and one disjunctive over a start-time array; this example is a
// self-contained random-instance version of that shape rather than a port of it.
//
// Two variants:
//
//   * by default, minimise the makespan, which under --prove produces a BOUNDS
//     proof;
//   * with --deadline N, ask instead whether any schedule finishes by time N,
//     which under --prove produces an UNSATISFIABLE proof when it does not.
//
// The machine is a control pair: --machine picks between the Disjunctive
// global (the default), the same relation as a Cumulative of capacity one, and
// the textbook pairwise-reified decomposition. All three say exactly the same
// thing about the schedule, so they differ only in propagation strength and in
// the shape of the proof.
//
// Instances are generated from --size and --seed, so no data file is needed;
// see rcpsp_instance.hh. Scale up with --size (more tasks), --max-duration
// (longer time horizon, so larger start-time domains) and --resources.
//
// The horizon is the makespan of a greedy serial schedule, which is a feasible
// schedule and so a valid upper bound on the optimum. Together with the
// precedence-only earliest start times and tails, that gives each start
// variable an initial domain that is a genuine relaxation of the problem, which
// is what keeps the proof's time-indexed encoding of Cumulative to a sensible
// size. The greedy schedule is checked from scratch by is_feasible() before its
// makespan is used, so a bug in the heuristic cannot quietly cut off the
// optimum.

#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>
#include <examples/rcpsp/rcpsp_instance.hh>

#include <algorithm>
#include <cstdlib>
#include <exception>
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
using std::max;
using std::min;
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

namespace
{
    // Build the variable ordering named by --branch, over the start variables
    // followed by the makespan.
    auto variable_order_from_string(const string & spec, const vector<IntegerVariableID> & vars) -> optional<BranchVariableHeuristic>
    {
        if (spec == "in-order")
            return variable_order::in_order(vars);
        if (spec == "dom-then-deg")
            return variable_order::dom_then_deg(vars);
        if (spec == "dom-wdeg")
            return variable_order::dom_wdeg(vars);
        if (spec.starts_with("dom-wdeg:")) {
            auto scheme = bench::scheme_from_string(spec.substr(spec.find(':') + 1));
            if (! scheme)
                return nullopt;
            return variable_order::dom_wdeg(vars, *scheme);
        }
        return nullopt;
    }

    // Build the value ordering named by --value-order. Splitting is the
    // interesting one for scheduling: a start-time domain over a long horizon
    // is bisected rather than enumerated.
    auto value_order_from_string(const string & spec) -> optional<BranchValueGenerator>
    {
        if (spec == "smallest")
            return value_order::smallest_first();
        if (spec == "split")
            return value_order::split_smallest_first();
        return nullopt;
    }

    auto print_instance(const rcpsp::Instance & inst) -> void
    {
        vector<char> needs_machine(inst.n_tasks, 0);
        for (auto & i : inst.machine_tasks)
            needs_machine[i] = 1;

        println("tasks:");
        for (int i = 0; i < inst.n_tasks; ++i) {
            print("  task {}: duration {}", i, inst.durations[i]);
            for (std::size_t r = 0; r < inst.capacities.size(); ++r)
                print(" resource{}={}", r, inst.demands[r][i]);
            println("{}", needs_machine[i] ? " machine" : "");
        }
        print("capacities:");
        for (auto & c : inst.capacities)
            print(" {}", c);
        println("");
        print("precedences:");
        for (const auto & [i, j] : inst.precedences)
            print(" {}->{}", i, j);
        println("");
        print("machine tasks:");
        for (auto & i : inst.machine_tasks)
            print(" {}", i);
        println("");
    }
}

auto main(int argc, char * argv[]) -> int
{
    cxxopts::Options options("RCPSP");
    cxxopts::ParseResult options_vars;

    try {
        options.add_options("Program")                                            //
            ("help", "Display help information")                                  //
            ("prove", "Create a proof")                                           //
            ("proof-files-basename", "Basename for the .opb and .pbp files",      //
                cxxopts::value<string>()->default_value("rcpsp"))                 //
            ("stats", "Print full solve statistics")                              //
            ("timeout", "Abort the solve after this many seconds (0 = no limit)", //
                cxxopts::value<double>()->default_value("0"))                     //
            ;

        options.add_options("Instance")                                                                      //
            ("size", "Number of tasks", cxxopts::value<int>()->default_value("8"))                           //
            ("seed", "Seed for instance generation", cxxopts::value<unsigned>()->default_value("0"))         //
            ("resources", "Number of renewable resources, each posted as a Cumulative",                      //
                cxxopts::value<int>()->default_value("2"))                                                   //
            ("capacity", "Capacity of each renewable resource", cxxopts::value<int>()->default_value("5"))   //
            ("max-duration", "Longest task duration; also scales the time horizon",                          //
                cxxopts::value<int>()->default_value("4"))                                                   //
            ("max-demand", "Largest demand a task can place on a resource, zero meaning it does not use it", //
                cxxopts::value<int>()->default_value("3"))                                                   //
            ("density",
                "Probability of a precedence between two tasks close together in the topological " //
                "order",                                                                           //
                cxxopts::value<double>()->default_value("0.3"))                                    //
            ("machine-fraction", "Probability that a task also needs the unary machine",           //
                cxxopts::value<double>()->default_value("0.35"))                                   //
            ("print-instance", "Print the generated instance before solving")                      //
            ;

        options.add_options("Model")                                                                //
            ("deadline", "Solve the decision variant: is there a schedule finishing by this time?", //
                cxxopts::value<long long>())                                                        //
            ("machine",
                "How to post the unary machine resource: disjunctive (the Disjunctive global, the " //
                "default), cumulative (a Cumulative of capacity one), or pairwise (reified "        //
                "non-overlap clauses)",                                                             //
                cxxopts::value<string>()->default_value("disjunctive"))                             //
            ("branch",
                "Branching variable order: in-order (default), dom-then-deg, or dom-wdeg[:VARIANT]" //
                " (VARIANT = classic / ia / ca / id / cd / ca.cd / chs)",                           //
                cxxopts::value<string>()->default_value("in-order"))                                //
            ("value-order",
                "Branching value order: smallest (default) or split, which bisects a start " //
                "time's domain rather than enumerating it",                                  //
                cxxopts::value<string>()->default_value("smallest"))                         //
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
        println("Schedule a random project of tasks with durations, resource demands and");
        println("precedences, minimising the makespan. With --deadline, instead decide whether");
        println("any schedule finishes by the given time.");
        println("");
        cout << options.help() << std::endl;
        return EXIT_SUCCESS;
    }

    rcpsp::Instance instance;
    try {
        rcpsp::GeneratorOptions gen_opts;
        gen_opts.n_tasks = options_vars["size"].as<int>();
        gen_opts.seed = options_vars["seed"].as<unsigned>();
        gen_opts.n_resources = options_vars["resources"].as<int>();
        gen_opts.capacity = options_vars["capacity"].as<int>();
        gen_opts.max_duration = options_vars["max-duration"].as<int>();
        gen_opts.max_demand = options_vars["max-demand"].as<int>();
        gen_opts.precedence_density = options_vars["density"].as<double>();
        gen_opts.machine_fraction = options_vars["machine-fraction"].as<double>();
        instance = rcpsp::generate(gen_opts);
    }
    catch (const std::exception & e) {
        println(cerr, "Error building instance: {}", e.what());
        return EXIT_FAILURE;
    }

    if (options_vars.contains("print-instance"))
        print_instance(instance);

    // A greedy serial schedule gives a feasible solution, so its makespan is an
    // upper bound on the optimum, and the critical path gives a lower bound.
    // Only trust the greedy schedule if an independent check agrees it really
    // is feasible; otherwise fall back to the trivial bound of scheduling
    // everything one task after another.
    auto greedy = rcpsp::serial_schedule(instance);
    auto greedy_makespan = rcpsp::makespan_of(instance, greedy);
    if (! rcpsp::is_feasible(instance, greedy)) {
        println(cerr, "Warning: the greedy schedule did not check out, falling back to a serial horizon.");
        greedy_makespan = 0;
        for (auto & d : instance.durations)
            greedy_makespan += d.raw_value;
    }

    auto critical_path = rcpsp::critical_path_length(instance);

    // In the decision variant the horizon comes down to the deadline, but never
    // below the critical path, so that no start variable ends up with an empty
    // domain. A deadline below the critical path is then enforced by an
    // explicit bound on the makespan instead, and the solver refutes it.
    auto deadline = options_vars.contains("deadline") ? optional<long long>{options_vars["deadline"].as<long long>()} : nullopt;
    auto horizon = deadline ? max(critical_path, min(*deadline, greedy_makespan)) : greedy_makespan;

    auto est = rcpsp::earliest_starts(instance);
    auto tail = rcpsp::tails(instance);

    Problem problem;

    vector<IntegerVariableID> starts;
    for (int i = 0; i < instance.n_tasks; ++i) {
        auto latest = horizon - instance.durations[i].raw_value - tail[i];
        starts.push_back(problem.create_integer_variable(Integer{est[i]}, Integer{latest}, "start" + to_string(i)));
    }

    auto makespan = problem.create_integer_variable(0_i, Integer{horizon}, "makespan");

    for (const auto & [i, j] : instance.precedences)
        problem.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * starts[j] + -1_i * starts[i], instance.durations[i]});

    for (int i = 0; i < instance.n_tasks; ++i)
        problem.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * makespan + -1_i * starts[i], instance.durations[i]});

    for (std::size_t r = 0; r < instance.capacities.size(); ++r)
        problem.post(Cumulative{starts, instance.durations, instance.demands[r], instance.capacities[r]});

    vector<IntegerVariableID> machine_starts;
    vector<Integer> machine_durations;
    for (auto & i : instance.machine_tasks) {
        machine_starts.push_back(starts[i]);
        machine_durations.push_back(instance.durations[i]);
    }

    // The three ways of saying that the machine does one thing at a time. Every
    // duration here is at least one, so the strict / non-strict distinction
    // does not arise, and the Cumulative form is exactly the Disjunctive one.
    auto machine_variant = options_vars["machine"].as<string>();
    if (machine_variant != "disjunctive" && machine_variant != "cumulative" && machine_variant != "pairwise") {
        println(cerr, "Error: unknown --machine value '{}'. Supported: disjunctive, cumulative, pairwise.", machine_variant);
        return EXIT_FAILURE;
    }
    if (machine_starts.size() >= 2) {
        if (machine_variant == "disjunctive")
            problem.post(Disjunctive{machine_starts, machine_durations});
        else if (machine_variant == "cumulative")
            problem.post(Cumulative{machine_starts, machine_durations, vector<Integer>(machine_starts.size(), 1_i), 1_i});
        else
            for (std::size_t a = 0; a < machine_starts.size(); ++a)
                for (auto b = a + 1; b < machine_starts.size(); ++b) {
                    auto first = problem.create_integer_variable(0_i, 1_i, "machine_before" + to_string(a) + "_" + to_string(b));
                    problem.post(LinearGreaterThanEqualIf{
                        WeightedSum{} + 1_i * machine_starts[b] + -1_i * machine_starts[a], machine_durations[a], first == 1_i});
                    problem.post(LinearGreaterThanEqualIf{
                        WeightedSum{} + 1_i * machine_starts[a] + -1_i * machine_starts[b], machine_durations[b], first == 0_i});
                }
    }

    // A deadline that the horizon already enforces needs nothing more; one
    // below the critical path does, because the horizon could not be brought
    // down that far without emptying a start variable's domain.
    if (! deadline)
        problem.minimise(makespan);
    else if (*deadline < horizon)
        problem.post(LessThanEqual{makespan, constant_variable(Integer{*deadline})});

    auto branch_vars = starts;
    branch_vars.push_back(makespan);

    auto var_order = variable_order_from_string(options_vars["branch"].as<string>(), branch_vars);
    if (! var_order) {
        println(cerr, "Error: unknown --branch value '{}'.", options_vars["branch"].as<string>());
        return EXIT_FAILURE;
    }
    auto val_order = value_order_from_string(options_vars["value-order"].as<string>());
    if (! val_order) {
        println(cerr, "Error: unknown --value-order value '{}'.", options_vars["value-order"].as<string>());
        return EXIT_FAILURE;
    }

    optional<Integer> best_makespan;
    vector<Integer> best_starts;
    bool proven = false;

    auto stats = bench::solve_with_timeout(options_vars["timeout"].as<double>(), problem,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                           best_makespan = s(makespan);
                           best_starts.clear();
                           for (auto & v : starts)
                               best_starts.push_back(s(v));
                           // Optimising, so keep going and let the solver prove
                           // this is the best; deciding, so the first schedule
                           // that meets the deadline is the whole answer.
                           return ! deadline.has_value();
                       },
            .branch = branch_with(*var_order, *val_order),
            .completed = [&]() { proven = true; }},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    string status;
    if (best_makespan)
        status = deadline ? "satisfiable" : (proven ? "optimal" : "timeout");
    else
        status = proven ? "infeasible" : "timeout-nosolution";

    println("instance: {}", instance.description);
    println("precedences: {}", instance.precedences.size());
    println("machine tasks: {}", instance.machine_tasks.size());
    println("machine posted as: {}", machine_variant);
    println("critical path: {}", critical_path);
    println("horizon: {}", horizon);
    println("status: {}", status);
    if (best_makespan) {
        println("makespan: {}", *best_makespan);
        print("schedule:");
        for (auto & v : best_starts)
            print(" {}", v);
        println("");
    }
    println("recursions: {}", stats.recursions);
    println("propagations: {}", stats.propagations);
    println("wall_time_s: {:.6f}", static_cast<double>(stats.solve_time.count()) / 1.0e6);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
