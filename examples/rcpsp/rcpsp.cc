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
// Three variants:
//
//   * by default, minimise the makespan, which under --prove produces a BOUNDS
//     proof;
//   * with --deadline N, ask instead whether any schedule finishes by time N,
//     which under --prove produces an UNSATISFIABLE proof when it does not;
//   * with --all, enumerate every feasible schedule instead of optimising.
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
// RCPSP/max
// ---------
//
// With --max-lag-density, the generator also lays *maximum* time lags on the
// precedence network: S_j - S_i <= L(i, j) + slack, where L is the longest path
// the precedences already force between the pair. A maximum lag is a backward
// arc of negative weight, so the network of lags acquires cycles, and a
// near-tight cycle is infeasible-or-nearly-so in a way per-constraint bounds
// propagation can only find by crawling. That is RCPSP/max, and it is the
// family a global difference-logic propagator is expected to win on;
// --infeasible closes a negative cycle of weight -1 outright.
//
// --file reads a real single-mode RCPSP/max instance in ProGen/max .sch format
// (the UBO, CD and SM sets), whose arcs are all generalised lags.
//
// Every time lag is a difference constraint, S_i - S_j <= -d, and so is each
// "the makespan is at least this task's end" bound. model_edges() below builds
// all of them as one list, in posting order, so that a later --variant flag can
// hand exactly that list to one global propagator instead.
//
// Maximum lags are off by default, and the generator's maximum-lag stage draws
// no random numbers at all when they are: this example is part of the proof
// benchmark set (issues #632, #633), so every pre-existing --size/--seed
// instance, its horizon, and its posting order all have to stay put.
//
// The horizon is the makespan of a greedy serial schedule, which is a feasible
// schedule and so a valid upper bound on the optimum. Together with the
// precedence-only earliest start times and tails, that gives each start
// variable an initial domain that is a genuine relaxation of the problem, which
// is what keeps the proof's time-indexed encoding of Cumulative to a sensible
// size. The greedy schedule is checked from scratch by is_feasible() before its
// makespan is used, so a bug in the heuristic cannot quietly cut off the
// optimum.
//
// With maximum lags that check is what does the work: the greedy schedule does
// not know about them, so one that violates a lag is rejected and the horizon
// falls back to rcpsp::default_horizon. That fallback is a proven bound only
// when there are no maximum lags --- RCPSP/max feasibility is NP-hard, so there
// is no cheap valid horizon, and --horizon is there to set one by hand.

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
        if (! inst.lags.empty()) {
            print("lags:");
            for (const auto & l : inst.lags)
                print(" {}->{}[{}]", l.from, l.to, l.d);
            println("");
        }
        print("machine tasks:");
        for (auto & i : inst.machine_tasks)
            print(" {}", i);
        println("");
    }

    // One difference constraint, s_from + d <= s_to, over the model's variables
    // rather than over task indices, so that the makespan bounds are the same
    // kind of thing as the time lags. Posted below as a two-term linear.
    struct ModelEdge
    {
        IntegerVariableID from;
        IntegerVariableID to;
        Integer d;
    };

    // Every difference constraint in the model, in one list and in posting
    // order: the plain precedences, then any generalised lags, then the
    // makespan bounds. Building the list separately from posting it is what
    // lets a later --variant hand the identical edge set, in the identical
    // order, to a single global propagator instead of to one linear each.
    [[nodiscard]] auto model_edges(const rcpsp::Instance & inst, const vector<IntegerVariableID> & starts, IntegerVariableID makespan)
        -> vector<ModelEdge>
    {
        vector<ModelEdge> edges;
        edges.reserve(inst.precedences.size() + inst.lags.size() + starts.size());

        // A precedence is finish-to-start: task i must be over before j starts.
        for (const auto & [i, j] : inst.precedences)
            edges.push_back(ModelEdge{starts[static_cast<std::size_t>(i)], starts[static_cast<std::size_t>(j)], inst.durations[i]});

        for (const auto & l : inst.lags)
            edges.push_back(ModelEdge{starts[static_cast<std::size_t>(l.from)], starts[static_cast<std::size_t>(l.to)], l.d});

        // The makespan is at least where each task ends.
        for (std::size_t i = 0; i < starts.size(); ++i)
            edges.push_back(ModelEdge{starts[i], makespan, inst.durations[i]});

        return edges;
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
            ("file",                                                                               //
                "Read a single-mode RCPSP/max instance from PATH, in ProGen/max .sch format (the " //
                "UBO, CD and SM sets), instead of generating one",                                 //
                cxxopts::value<string>())                                                          //
            ("max-lag-density",
                "Probability that a pair joined by a precedence path also gets a maximum time " //
                "lag, which is what turns this into an RCPSP/max instance. Zero, the default, " //
                "draws no random numbers at all, so every instance generated without it is "    //
                "unchanged",                                                                    //
                cxxopts::value<double>()->default_value("0"))                                   //
            ("max-lag-span", "A maximum time lag spans at most this many tasks",                //
                cxxopts::value<int>()->default_value("6"))                                      //
            ("max-lag-slack",
                "A generated maximum lag allows the longest path plus this much, so it closes a " //
                "cycle of exactly this weight: 0 is tight, small is near-tight",                  //
                cxxopts::value<long long>()->default_value("2"))                                  //
            ("infeasible",
                "Tighten one generated maximum lag one unit past its longest path, closing a "    //
                "negative cycle of weight -1. The instance is then unsatisfiable, but no single " //
                "constraint is violated by the initial domains")                                  //
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
            ("unary",
                "How to post a renewable resource whose capacity is one: cumulative (the "     //
                "default, so every resource is handled the same way and a variant comparison " //
                "is not confounded by which resources happen to be unary) or disjunctive",     //
                cxxopts::value<string>()->default_value("cumulative"))                         //
            ("horizon",
                "Override the planning horizon (0, the default, computes it from the " //
                "instance). A value below the optimum cuts off solutions",             //
                cxxopts::value<long long>()->default_value("0"))                       //
            ("all",
                "Enumerate every feasible schedule instead of minimising the makespan, posting " //
                "no objective")                                                                  //
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
        if (options_vars.contains("file"))
            instance = rcpsp::read_file(options_vars["file"].as<string>());
        else {
            rcpsp::GeneratorOptions gen_opts;
            gen_opts.n_tasks = options_vars["size"].as<int>();
            gen_opts.seed = options_vars["seed"].as<unsigned>();
            gen_opts.n_resources = options_vars["resources"].as<int>();
            gen_opts.capacity = options_vars["capacity"].as<int>();
            gen_opts.max_duration = options_vars["max-duration"].as<int>();
            gen_opts.max_demand = options_vars["max-demand"].as<int>();
            gen_opts.precedence_density = options_vars["density"].as<double>();
            gen_opts.machine_fraction = options_vars["machine-fraction"].as<double>();
            gen_opts.max_lag_density = options_vars["max-lag-density"].as<double>();
            gen_opts.max_lag_span = options_vars["max-lag-span"].as<int>();
            gen_opts.max_lag_slack = options_vars["max-lag-slack"].as<long long>();
            gen_opts.infeasible = options_vars.contains("infeasible");
            instance = rcpsp::generate(gen_opts);
        }
    }
    catch (const std::exception & e) {
        println(cerr, "Error building instance: {}", e.what());
        return EXIT_FAILURE;
    }

    for (std::size_t r = 0; r < instance.capacities.size(); ++r)
        for (int i = 0; i < instance.n_tasks; ++i)
            if (instance.demands[r][i] > instance.capacities[r]) {
                println(cerr, "Error: task {} demands more of resource {} than its capacity.", i, r);
                return EXIT_FAILURE;
            }

    if (options_vars.contains("print-instance"))
        print_instance(instance);

    // A greedy serial schedule gives a feasible solution, so its makespan is an
    // upper bound on the optimum, and the critical path gives a lower bound.
    // Only trust the greedy schedule if an independent check agrees it really
    // is feasible; otherwise fall back to the standard planning horizon.
    //
    // serial_schedule() knows about precedences, resources and the machine, but
    // not about generalised lags, so on an RCPSP/max instance its schedule may
    // well violate a maximum lag. is_feasible() does check the lags, so that
    // case lands in the fallback rather than silently cutting off the optimum.
    // Note the fallback is only a *proven* upper bound when there are no maximum
    // lags: RCPSP/max feasibility is NP-hard, and there is no cheap valid
    // horizon. See rcpsp::default_horizon.
    auto greedy = rcpsp::serial_schedule(instance);
    auto greedy_makespan = rcpsp::makespan_of(instance, greedy);
    if (! rcpsp::is_feasible(instance, greedy)) {
        if (! rcpsp::has_maximum_lags(instance))
            println(cerr, "Warning: the greedy schedule did not check out, falling back to a serial horizon.");
        greedy_makespan = rcpsp::default_horizon(instance);
    }

    auto critical_path = rcpsp::critical_path_length(instance);

    auto horizon_override = options_vars["horizon"].as<long long>();
    if (horizon_override < 0) {
        println(cerr, "Error: --horizon must be non-negative.");
        return EXIT_FAILURE;
    }
    if (horizon_override > 0)
        greedy_makespan = horizon_override;

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

    auto unary_variant = options_vars["unary"].as<string>();
    if (unary_variant != "cumulative" && unary_variant != "disjunctive") {
        println(cerr, "Error: unknown --unary value '{}'. Supported: cumulative, disjunctive.", unary_variant);
        return EXIT_FAILURE;
    }

    // The temporal network, as one two-term linear per edge. Spelled
    // GreaterThanEqual with the head first, which is the direction a precedence
    // reads in, and which every one of these has been posted in since this
    // example landed.
    for (const auto & e : model_edges(instance, starts, makespan))
        problem.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * e.to + -1_i * e.from, e.d});

    // A .sch instance's dummy source is pinned at time zero: the file's arc
    // weights are all relative to it.
    if (instance.source_task)
        problem.post(LinearLessThanEqual{WeightedSum{} + 1_i * starts[static_cast<std::size_t>(*instance.source_task)], 0_i});

    for (std::size_t r = 0; r < instance.capacities.size(); ++r) {
        // A task that runs for no time never occupies a resource, so leaving it
        // out changes nothing but keeps the propagator and the proof smaller.
        // Every generated duration is at least one, so nothing is ever dropped
        // there and the Cumulative posted below is exactly the one this example
        // has always posted; a .sch instance's dummy source and sink do drop out.
        vector<IntegerVariableID> task_starts;
        vector<Integer> task_durations, task_demands;
        for (int i = 0; i < instance.n_tasks; ++i)
            if (instance.durations[i] > 0_i) {
                task_starts.push_back(starts[i]);
                task_durations.push_back(instance.durations[i]);
                task_demands.push_back(instance.demands[r][i]);
            }
        if (task_starts.empty())
            continue;

        if (unary_variant == "disjunctive" && instance.capacities[r] == 1_i) {
            // Disjunctive carries no demands, so unlike Cumulative it cannot be
            // handed a task that does not use this resource: a zero-demand task
            // left in would be wrongly forbidden from overlapping.
            vector<IntegerVariableID> users;
            vector<Integer> user_durations;
            for (std::size_t i = 0; i < task_starts.size(); ++i)
                if (task_demands[i] > 0_i) {
                    users.push_back(task_starts[i]);
                    user_durations.push_back(task_durations[i]);
                }
            if (users.size() >= 2)
                problem.post(Disjunctive{users, user_durations});
        }
        else
            problem.post(Cumulative{task_starts, task_durations, task_demands, instance.capacities[r]});
    }

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

    auto all = options_vars.contains("all");

    // A deadline that the horizon already enforces needs nothing more; one
    // below the critical path does, because the horizon could not be brought
    // down that far without emptying a start variable's domain.
    if (deadline && *deadline < horizon)
        problem.post(LessThanEqual{makespan, constant_variable(Integer{*deadline})});

    // --all enumerates every schedule, so it posts no objective at all.
    if (! all && ! deadline)
        problem.minimise(makespan);

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
                           // Optimising or enumerating, so keep going and let
                           // the solver prove this is the best (or that there
                           // are no more); deciding, so the first schedule that
                           // meets the deadline is the whole answer.
                           return all || ! deadline.has_value();
                       },
            .branch = branch_with(*var_order, *val_order),
            .completed = [&]() { proven = true; }},
        options_vars.contains("prove") ? make_optional<ProofOptions>(options_vars["proof-files-basename"].as<string>()) : nullopt);

    string status;
    if (! best_makespan)
        status = proven ? "infeasible" : "timeout-nosolution";
    else if (all)
        status = proven ? "satisfiable-complete" : "timeout";
    else if (deadline)
        status = "satisfiable";
    else
        status = proven ? "optimal" : "timeout";

    auto max_lags = std::count_if(instance.lags.begin(), instance.lags.end(), [](const rcpsp::Lag & l) { return l.d < 0_i; });

    println("instance: {}", instance.description);
    println("precedences: {}", instance.precedences.size());
    println("lags: {}", instance.lags.size());
    println("max lags: {}", max_lags);
    println("machine tasks: {}", instance.machine_tasks.size());
    println("machine posted as: {}", machine_variant);
    println("unary posted as: {}", unary_variant);
    println("critical path: {}", critical_path);
    println("horizon: {}", horizon);
    println("all: {}", all ? "yes" : "no");
    println("status: {}", status);
    if (best_makespan) {
        println("makespan: {}", *best_makespan);
        print("schedule:");
        for (auto & v : best_starts)
            print(" {}", v);
        println("");
    }
    println("solutions: {}", stats.solutions);
    println("recursions: {}", stats.recursions);
    println("propagations: {}", stats.propagations);
    println("wall_time_s: {:.6f}", static_cast<double>(stats.solve_time.count()) / 1.0e6);

    if (options_vars.contains("stats"))
        print("{}", stats);

    return EXIT_SUCCESS;
}
