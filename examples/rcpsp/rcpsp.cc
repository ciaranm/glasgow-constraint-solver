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
// Inferred resources, and the makespan bound they carry
// -----------------------------------------------------
//
// --infer-disjunctive and --infer-cumulative run the two presolvers that read
// implied resources off the posted ones: cliques of tasks no single resource
// can hold pairwise, and cover inequalities lifted to non-unit heights. Each
// posts a derived Cumulative, adding nothing to the model.
//
// What such a constraint is worth is energy, and energy is a bound on the
// makespan: its tasks need a fixed number of resource-units out of something
// that supplies so many per time step. --infer-makespan-bound, on by default,
// has that bound *derived* rather than only reported, by naming the makespan
// variable to the presolvers. It is only a bound if the model says every task
// finishes by it, so the derivation sums the model's own
// `start + duration <= makespan` rows --- which exist under --variant=decomposed
// and --variant=presolved and not under --variant=global, where the whole
// temporal network is one propagator instead.
//
// --mutate-makespan-bound claims one more than the energy supports, which VeriPB
// must refuse. See dev_docs/certified-makespan-bounds.md.
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
#include <gcs/constraints/difference.hh>
#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/presolvers/difference_logic.hh>
#include <gcs/presolvers/inferred_cumulative/inferred_cumulative.hh>
#include <gcs/presolvers/inferred_disjunctive/inferred_disjunctive.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <examples/benchmark_cli.hh>
#include <examples/rcpsp/rcpsp_instance.hh>

#include <algorithm>
#include <cstddef>
#include <cstdlib>
#include <exception>
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
    // kind of thing as the time lags.
    struct ModelEdge
    {
        IntegerVariableID from;
        IntegerVariableID to;
        Integer d;

        // Set only for the pairwise machine decomposition under
        // --machine=difference, where each disjunct holds only under its
        // ordering Boolean. The temporal network's edges are unconditional.
        std::optional<IntegerVariableCondition> cond = nullopt;
    };

    // How the temporal network reaches the solver. All three say exactly the
    // same thing, over the same edges in the same order.
    enum struct Variant
    {
        Decomposed, ///< One two-term LinearGreaterThanEqual per edge.
        Presolved,  ///< As Decomposed, plus the DifferenceLogic presolver, which lifts them back.
        Global      ///< The whole network as one DifferenceConstraints.
    };

    auto variant_from_string(const string & spec) -> optional<Variant>
    {
        if (spec == "decomposed")
            return Variant::Decomposed;
        if (spec == "presolved")
            return Variant::Presolved;
        if (spec == "global")
            return Variant::Global;
        return nullopt;
    }

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
                "Probability of a precedence between two tasks close together in the topological "       //
                "order",                                                                                 //
                cxxopts::value<double>()->default_value("0.3"))                                          //
            ("machine-fraction", "Probability that a task also needs the unary machine",                 //
                cxxopts::value<double>()->default_value("0.35"))                                         //
            ("print-instance", "Print the generated instance before solving")                            //
            ("infer-disjunctive",                                                                        //
                "Run the InferredDisjunctive presolver, which looks for cliques of tasks that no "       //
                "single resource can hold pairwise and posts each as a derived capacity-one Cumulative", //
                cxxopts::value<bool>()->default_value("false"))                                          //
            ("infer-disjunctive-candidates",                                                             //
                "Cap how many candidate pairs the clique search grows (Sidorov's N_cover)",              //
                cxxopts::value<std::size_t>()->default_value("100"))                                     //
            ("infer-disjunctive-posted",                                                                 //
                "Cap how many cliques are posted (Sidorov's N_out)",                                     //
                cxxopts::value<std::size_t>()->default_value("5"))                                       //
            ("infer-disjunctive-min-clique-size",                                                        //
                "Smallest clique worth posting; two makes every conflicting pair a candidate, which "    //
                "is what Sidorov's binary covers are",                                                   //
                cxxopts::value<std::size_t>()->default_value("3"))                                       //
            ("infer-cumulative",                                                                         //
                "Run the InferredCumulative presolver, which lifts cover inequalities over the "         //
                "resources' capacity rows into implied Cumulatives with non-unit heights",               //
                cxxopts::value<bool>()->default_value("false"))                                          //
            ("infer-cumulative-covers",                                                                  //
                "Cap how many covers are grown and lifted (Sidorov's N_cover)",                          //
                cxxopts::value<std::size_t>()->default_value("100"))                                     //
            ("infer-cumulative-posted",                                                                  //
                "Cap how many lifted cuts are posted (Sidorov's N_out)",                                 //
                cxxopts::value<std::size_t>()->default_value("5"))                                       //
            ("infer-cumulative-lifting-calls",                                                           //
                "Cap how many lifting subproblems are solved (Sidorov's N_calls)",                       //
                cxxopts::value<std::size_t>()->default_value("20000"))                                   //
            ("mutate-makespan-bound",                                                                    //
                "Claim a makespan one larger than the inferred constraints' energy supports. For "       //
                "validating the bound only: VeriPB must reject the resulting proof, and a run that "     //
                "verifies is a finding about the honest derivation",                                     //
                cxxopts::value<bool>()->default_value("false"))                                          //
            ("infer-makespan-bound",                                                                     //
                "Have the inferring presolvers derive a lower bound on the makespan from each "          //
                "constraint they post, rather than only reporting one. Needs the model's "               //
                "`start + duration <= makespan` rows, so --variant=global does not have them",           //
                cxxopts::value<bool>()->default_value("true"))                                           //
            ("file",                                                                                     //
                "Read a single-mode RCPSP/max instance from PATH, in ProGen/max .sch format (the "       //
                "UBO, CD and SM sets), instead of generating one",                                       //
                cxxopts::value<string>())                                                                //
            ("dzn",                                                                                      //
                "Read a plain RCPSP instance from PATH, in the MiniZinc data format that goes with "     //
                "rcpsp.mzn (the Pack, Pack_d, PSPLib, la_x, ksd15_d and bl sets), instead of "           //
                "generating one",                                                                        //
                cxxopts::value<string>())                                                                //
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
                "How to post the unary machine resource: disjunctive (the Disjunctive global, the "   //
                "default), cumulative (a Cumulative of capacity one), pairwise (reified non-overlap " //
                "clauses), or difference (the same pairwise decomposition written as conditional "    //
                "difference constraints, which is what puts the machine into the difference "         //
                "network that --variant handles)",                                                    //
                cxxopts::value<string>()->default_value("disjunctive"))                               //
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
            ("disjunctive-overload",
                "Give every posted Disjunctive the overload check, off by default because its "   //
                "certificate is expensive enough that whether it pays is what #730 is measuring") //
            ("disjunctive-overload-certificate",
                "How to certify an overload: time-indexed (re-encode time in the proof), "     //
                "sorting-network (sort the window's tasks in the proof), or cheaper (the "     //
                "default, which picks per firing from the window's shape). Both run over the " //
                "one unchanged encoding, so this selects a proof strategy and not a model",    //
                cxxopts::value<string>()->default_value("cheaper"))                            //
            ("disjunctive-overload-crossover",
                "Where cheaper switches: emit the sorting network once the window's span "                      //
                "exceeds this many times the number of tasks in it. Set this to seven alongside "               //
                "--disjunctive-overload-derive-at-most-ones-again: without that amortisation the "              //
                "two certificates cross far earlier, and the pair of settings belongs together",                //
                cxxopts::value<std::size_t>()->default_value(to_string(DisjunctiveRules{}.overload_crossover))) //
            ("disjunctive-overload-derive-at-most-ones-again",
                "Derive the time-indexed certificate's per-time at-most-ones per firing rather " //
                "than keeping them and citing them again. Here so that what keeping them buys "  //
                "can be measured rather than believed")                                          //
            ("disjunctive-overload-temporary",
                "Introduce the overload certificate's activity flags per firing and let backtracking " //
                "delete them, rather than once at the proof's top level. Slower and larger, and here " //
                "so that #730's measurement can be repeated rather than believed")                     //
            ("disjunctive-overload-max-window",
                "Have the overload check decline a conflict whose smallest window holds more "  //
                "than this many tasks, its certificate being cubic in that. Zero, the default," //
                " takes every conflict",                                                        //
                cxxopts::value<std::size_t>()->default_value("0"))                              //
            ("horizon",
                "Override the planning horizon (0, the default, computes it from the " //
                "instance). A value below the optimum cuts off solutions",             //
                cxxopts::value<long long>()->default_value("0"))                       //
            ("all",
                "Enumerate every feasible schedule instead of minimising the makespan, posting " //
                "no objective")                                                                  //
            ("variant",
                "How to post the temporal network --- the precedences, the time lags and the "     //
                "makespan bounds, which are all difference constraints. decomposed (the default) " //
                "posts one two-term LinearGreaterThanEqual per edge; global posts the whole "      //
                "network as one DifferenceConstraints; presolved posts it decomposed and lets "    //
                "the DifferenceLogic presolver lift it back",                                      //
                cxxopts::value<string>()->default_value("decomposed"))                             //
            ("simplify",
                "Run the difference-logic root simplification stage (Johnson's all-pairs shortest " //
                "paths, then redundant-edge removal, condition fixing and node removal). On by "    //
                "default; --simplify=off turns it off. Ignored under --variant=decomposed, which "  //
                "has no difference propagator to simplify for",                                     //
                cxxopts::value<string>()->default_value("on"))                                      //
            ("incremental",
                "Propagate the difference system incrementally (a maintained potential function "  //
                "and Dijkstra on reduced costs) rather than re-running Bellman-Ford from scratch " //
                "on every wake. On by default; --incremental=off selects the from-scratch "        //
                "version, which must reach the identical fixpoint and so must search identically", //
                cxxopts::value<string>()->default_value("on"))                                     //
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
        if (options_vars.contains("file") && options_vars.contains("dzn"))
            throw std::runtime_error{"--file and --dzn both name an instance; give only one"};
        if (options_vars.contains("file"))
            instance = rcpsp::read_file(options_vars["file"].as<string>());
        else if (options_vars.contains("dzn"))
            instance = rcpsp::read_dzn_file(options_vars["dzn"].as<string>());
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

    auto variant_name = options_vars["variant"].as<string>();
    auto variant = variant_from_string(variant_name);
    if (! variant) {
        println(cerr, "Error: unknown --variant value '{}'. Supported: decomposed, presolved, global.", variant_name);
        return EXIT_FAILURE;
    }

    auto simplify_name = options_vars["simplify"].as<string>();
    if (simplify_name != "on" && simplify_name != "off") {
        println(cerr, "Error: --simplify must be on or off, not '{}'.", simplify_name);
        return EXIT_FAILURE;
    }
    auto simplify = (simplify_name == "on");
    auto simplification = std::make_shared<DifferenceSimplificationStats>();

    auto incremental_name = options_vars["incremental"].as<string>();
    if (incremental_name != "on" && incremental_name != "off") {
        println(cerr, "Error: --incremental must be on or off, not '{}'.", incremental_name);
        return EXIT_FAILURE;
    }
    auto incremental = (incremental_name == "on");

    // The temporal network. --variant decides how it reaches the solver, over
    // the identical edge list in the identical order, so a comparison between
    // the three is between the handling and nothing else.
    auto edges = model_edges(instance, starts, makespan);
    auto presolver_stats = std::make_shared<DifferenceLogicStats>();

    // --machine=difference puts the machine into that same network, as the
    // pairwise disjunctive decomposition written in conditional edges: one
    // Boolean per pair, and the two disjuncts as edges holding under it and
    // under its negation. It has to be built before the network is posted so
    // that both end up in the *same* DifferenceConstraints under
    // --variant=global --- a cycle that closes only through an ordering
    // decision spans both halves, and two separate propagators would never see
    // it. Nothing here runs in any other --machine mode, so no other path
    // creates a variable or posts a row it did not create or post before.
    vector<IntegerVariableID> machine_starts;
    vector<Integer> machine_durations;
    for (auto & i : instance.machine_tasks) {
        machine_starts.push_back(starts[i]);
        machine_durations.push_back(instance.durations[i]);
    }

    auto machine_variant = options_vars["machine"].as<string>();
    if (machine_variant != "disjunctive" && machine_variant != "cumulative" && machine_variant != "pairwise" && machine_variant != "difference") {
        println(cerr, "Error: unknown --machine value '{}'. Supported: disjunctive, cumulative, pairwise, difference.", machine_variant);
        return EXIT_FAILURE;
    }

    vector<IntegerVariableID> machine_order_vars;
    if (machine_variant == "difference" && machine_starts.size() >= 2)
        for (std::size_t a = 0; a < machine_starts.size(); ++a)
            for (auto b = a + 1; b < machine_starts.size(); ++b) {
                auto first = problem.create_integer_variable(0_i, 1_i, "machine_before" + to_string(a) + "_" + to_string(b));
                machine_order_vars.push_back(first);
                edges.push_back(ModelEdge{machine_starts[a], machine_starts[b], machine_durations[a], first == 1_i});
                edges.push_back(ModelEdge{machine_starts[b], machine_starts[a], machine_durations[b], first == 0_i});
            }

    switch (*variant) {
        using enum Variant;
    case Presolved:
    case Decomposed:
        // One two-term linear per edge, spelled GreaterThanEqual with the head
        // first, which is the direction a precedence reads in and the spelling
        // every one of these has been posted in since this example landed.
        // Changing it would give the same constraint a different WeightedSum
        // term order, and so a different OPB row, for no reason.
        //
        // A LessThanEqual over an offset view would say the same thing, and the
        // presolver lifts either --- both emit the same @c[<id>] row --- so the
        // spelling here is a byte-identity choice and not a citability one.
        // examples/difference_chain --donor is where the two are measured
        // against each other.
        for (const auto & e : edges) {
            auto sum = WeightedSum{} + 1_i * e.to + -1_i * e.from;
            if (e.cond)
                problem.post(LinearGreaterThanEqualIf{sum, e.d, *e.cond});
            else
                problem.post(LinearGreaterThanEqual{sum, e.d});
        }
        if (*variant == Presolved)
            problem.add_presolver(DifferenceLogic{presolver_stats}
                    .simplifying_at_root(simplify)
                    .reporting_simplification_to(simplification)
                    .incrementally(incremental));
        break;

    case Global:
        // The whole network as one propagator. A ModelEdge is s_from + d <= s_to,
        // and a DifferenceEdge is x - y <= d, so the weight flips sign.
        {
            vector<DifferenceEdge> difference_edges;
            difference_edges.reserve(edges.size());
            for (const auto & e : edges)
                difference_edges.push_back(DifferenceEdge{e.from, e.to, -e.d, e.cond});
            problem.post(DifferenceConstraints{difference_edges}
                    .simplifying_at_root(simplify)
                    .reporting_simplification_to(simplification)
                    .incrementally(incremental));
        }
        break;
    }

    // A .sch instance's dummy source is pinned at time zero: the file's arc
    // weights are all relative to it.
    if (instance.source_task)
        problem.post(LinearLessThanEqual{WeightedSum{} + 1_i * starts[static_cast<std::size_t>(*instance.source_task)], 0_i});

    // Off unless asked for: the overload check has no certificate, so this is a
    // measurement switch rather than a model choice. See #730.
    DisjunctiveRules disjunctive_rules;
    disjunctive_rules.overload = options_vars["disjunctive-overload"].as<bool>();
    disjunctive_rules.overload_max_window = options_vars["disjunctive-overload-max-window"].as<std::size_t>();
    if (options_vars["disjunctive-overload-temporary"].as<bool>())
        disjunctive_rules.overload_vocabulary_at = gcs::innards::ProofLevel::Temporary;
    disjunctive_rules.overload_cache_bridge = ! options_vars["disjunctive-overload-derive-at-most-ones-again"].as<bool>();
    disjunctive_rules.overload_crossover = options_vars["disjunctive-overload-crossover"].as<std::size_t>();
    {
        auto which = options_vars["disjunctive-overload-certificate"].as<string>();
        if (which == "time-indexed")
            disjunctive_rules.overload_certificate = DisjunctiveOverloadCertificate::TimeIndexed;
        else if (which == "sorting-network")
            disjunctive_rules.overload_certificate = DisjunctiveOverloadCertificate::SortingNetwork;
        else if (which == "cheaper")
            disjunctive_rules.overload_certificate = DisjunctiveOverloadCertificate::Cheaper;
        else {
            println(cerr, "unknown --disjunctive-overload-certificate {}", which);
            return EXIT_FAILURE;
        }
    }

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
                problem.post(Disjunctive{users, user_durations}.with_rules(disjunctive_rules));
        }
        else
            problem.post(Cumulative{task_starts, task_durations, task_demands, instance.capacities[r]});
    }

    // The four ways of saying that the machine does one thing at a time. Every
    // duration here is at least one, so the strict / non-strict distinction
    // does not arise, and the Cumulative form is exactly the Disjunctive one.
    // The difference form was posted above, with the temporal network, because
    // it has to share a propagator with it.
    if (machine_variant != "difference" && machine_starts.size() >= 2) {
        if (machine_variant == "disjunctive")
            problem.post(Disjunctive{machine_starts, machine_durations}.with_rules(disjunctive_rules));
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

    // Added after every Cumulative above, because what it has to work with is
    // the set of posted resources: it looks for pairs of tasks that some
    // resource cannot hold together, and grows those into cliques.
    //
    // Naming the makespan is what turns each posted constraint's capacity bound
    // from a number the presolver reports into one the proof contains: the
    // model's `start + duration <= makespan` rows confine the tasks to a
    // window, and the constraint's energy then says how wide that window has to
    // be. Those rows exist under --variant=decomposed and --variant=presolved;
    // --variant=global puts the whole temporal network into one propagator
    // instead, so there is no per-task row to sum and the bound falls back to
    // whatever the tasks' own domains give.
    auto infer_makespan_bound = options_vars["infer-makespan-bound"].as<bool>();
    auto mutate_makespan_bound = options_vars["mutate-makespan-bound"].as<bool>();

    auto disjunctive_stats = std::make_shared<InferredDisjunctiveStats>();
    auto infer_disjunctive = options_vars["infer-disjunctive"].as<bool>();
    if (infer_disjunctive) {
        auto presolver = InferredDisjunctive{disjunctive_stats}
                             .with_budgets(options_vars["infer-disjunctive-candidates"].as<std::size_t>(),
                                 options_vars["infer-disjunctive-posted"].as<std::size_t>())
                             .with_minimum_clique_size(options_vars["infer-disjunctive-min-clique-size"].as<std::size_t>());
        if (infer_makespan_bound)
            presolver.with_makespan(makespan);
        if (mutate_makespan_bound)
            presolver.with_proof_mutation(gcs::innards::inferred_disjunctive_mutation::ClaimHigherMakespanBound{});
        problem.add_presolver(presolver);
    }

    auto cumulative_stats = std::make_shared<InferredCumulativeStats>();
    auto infer_cumulative = options_vars["infer-cumulative"].as<bool>();
    if (infer_cumulative) {
        auto presolver =
            InferredCumulative{cumulative_stats}
                .with_budgets(options_vars["infer-cumulative-covers"].as<std::size_t>(), options_vars["infer-cumulative-posted"].as<std::size_t>())
                .with_lifting_call_budget(options_vars["infer-cumulative-lifting-calls"].as<std::size_t>());
        if (infer_makespan_bound)
            presolver.with_makespan(makespan);
        if (mutate_makespan_bound)
            presolver.with_proof_mutation(gcs::innards::inferred_cumulative_mutation::ClaimHigherMakespanBound{});
        problem.add_presolver(presolver);
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

    // Under --machine=difference the ordering Booleans have to be branched on,
    // and first. DifferenceConstraints makes no inference about an edge's
    // condition at all --- that is the paper's IncImp, deliberately not
    // implemented (see dev_docs/difference-logic.md) --- so an edge whose
    // Boolean is unfixed simply does not constrain, and leaving them out of the
    // branch list would let the solver report a schedule that runs two machine
    // tasks at once. The reified linear forms do infer their condition, which is
    // why --machine=pairwise is sound without them; relying on that here would
    // be relying on the very thing this variant is meant to exercise.
    auto branch_vars = machine_order_vars;
    branch_vars.insert(branch_vars.end(), starts.begin(), starts.end());
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
    println("variant: {}", variant_name);
    if (*variant == Variant::Presolved) {
        println("presolver_edges_lifted: {}", presolver_stats->edges_lifted);
        println("presolver_nodes: {}", presolver_stats->nodes);
    }
    if (infer_disjunctive) {
        println("inferred_disjunctive_conflicting_pairs: {}", disjunctive_stats->conflicting_pairs);
        println("inferred_disjunctive_cross_donor_pairs: {}", disjunctive_stats->cross_donor_pairs);
        println("inferred_disjunctive_cliques_found: {}", disjunctive_stats->cliques_found);
        println("inferred_disjunctive_cliques_posted: {}", disjunctive_stats->cliques_posted);
        println("inferred_disjunctive_clique_members_posted: {}", disjunctive_stats->clique_members_posted);
        // Sidorov's L: a makespan lower bound that needs no search to believe.
        println("inferred_disjunctive_capacity_bound: {}", disjunctive_stats->largest_capacity_bound.raw_value);
        // What of that L the proof actually contains.
        println("inferred_disjunctive_certified_bound: {}", disjunctive_stats->certified_makespan_bound.raw_value);
    }
    if (infer_cumulative) {
        println("inferred_cumulative_tasks: {}", cumulative_stats->tasks);
        println("inferred_cumulative_covers_considered: {}", cumulative_stats->covers_considered);
        println("inferred_cumulative_lifting_subproblems: {}", cumulative_stats->lifting_subproblems);
        println("inferred_cumulative_cuts_found: {}", cumulative_stats->cuts_found);
        println("inferred_cumulative_cuts_uncertifiable: {}", cumulative_stats->cuts_uncertifiable);
        println("inferred_cumulative_cuts_posted: {}", cumulative_stats->cuts_posted);
        println("inferred_cumulative_non_unit_cuts_posted: {}", cumulative_stats->non_unit_cuts_posted);
        println("inferred_cumulative_capacity_bound: {}", cumulative_stats->largest_capacity_bound.raw_value);
        println("inferred_cumulative_certified_bound: {}", cumulative_stats->certified_makespan_bound.raw_value);
    }
    if (*variant != Variant::Decomposed) {
        println("simplify: {}", simplify_name);
        println("incremental: {}", incremental_name);
        println("simplify_ran: {}", simplification->ran ? "yes" : "no");
        println("simplify_redundant_edges_removed: {}", simplification->redundant_edges_removed);
        println("simplify_conditions_fixed: {}", simplification->conditions_fixed);
        println("simplify_isolated_nodes_removed: {}", simplification->isolated_nodes_removed);
    }
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
