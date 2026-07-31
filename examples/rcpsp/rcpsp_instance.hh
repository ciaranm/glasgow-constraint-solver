#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_RCPSP_INSTANCE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_RCPSP_INSTANCE_HH

// Instance model, random generator and schedule utilities for the RCPSP
// example. Kept separate from the model itself (rcpsp.cc) so that the model
// file reads as a model.
//
// An instance has n tasks, indexed 0..n-1. Task i has an integer duration
// d_i >= 1 and, for each of the renewable resources, a demand q_{r,i} >= 0
// (zero meaning "does not use that resource"). A precedence (i, j) means task i
// must finish before task j starts. Some tasks additionally need a single
// machine that can only do one thing at a time.
//
// Precedences are always generated with i < j, so the task indices are already
// a topological order of the precedence DAG: earliest_starts() and tails()
// below rely on that, and generate() is the only thing that builds the list.

#include <gcs/integer.hh>

#include <algorithm>
#include <cstdint>
#include <random>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace rcpsp
{
    struct Instance
    {
        int n_tasks = 0;

        /// Duration of each task, at least one.
        std::vector<gcs::Integer> durations;

        /// Capacity of each renewable resource.
        std::vector<gcs::Integer> capacities;

        /// demands[r][i] is how much of resource r task i needs while it runs.
        std::vector<std::vector<gcs::Integer>> demands;

        /// Precedences (i, j), always with i < j: task i must finish before
        /// task j starts.
        std::vector<std::pair<int, int>> precedences;

        /// The tasks that also need the single unary machine, ascending.
        std::vector<int> machine_tasks;

        std::string description;
    };

    /// Parameters for generate(). The defaults are the small instance the
    /// example runs when given no options.
    struct GeneratorOptions
    {
        int n_tasks = 8;
        std::uint_fast32_t seed = 0;
        int n_resources = 2;
        int capacity = 5;
        int max_duration = 4;
        int max_demand = 3;

        /// Probability of a precedence between two tasks whose indices differ
        /// by at most precedence_window. Restricting to a window keeps the
        /// project network shallow and mostly free of transitive edges, which
        /// is what a real project network looks like.
        double precedence_density = 0.3;
        int precedence_window = 4;

        /// Probability that a task also needs the unary machine.
        double machine_fraction = 0.35;
    };

    /// Build a random instance. Everything is derived from the seed, so an
    /// instance is reproducible from its command line alone.
    [[nodiscard]] inline auto generate(const GeneratorOptions & opts) -> Instance
    {
        if (opts.n_tasks < 1)
            throw std::runtime_error{"need at least one task"};
        if (opts.n_resources < 0)
            throw std::runtime_error{"cannot have a negative number of resources"};
        if (opts.max_duration < 1)
            throw std::runtime_error{"the largest duration must be at least one"};
        if (opts.max_demand < 0)
            throw std::runtime_error{"cannot have a negative largest demand"};
        if (opts.max_demand > opts.capacity)
            throw std::runtime_error{"a task can demand more than a resource's capacity, so the instance is trivially infeasible"};

        Instance inst;
        inst.n_tasks = opts.n_tasks;
        inst.description = "random n=" + std::to_string(opts.n_tasks) + " seed=" + std::to_string(opts.seed) +
            " resources=" + std::to_string(opts.n_resources) + " capacity=" + std::to_string(opts.capacity) +
            " max-duration=" + std::to_string(opts.max_duration) + " max-demand=" + std::to_string(opts.max_demand);

        std::mt19937 rng{opts.seed};
        std::uniform_int_distribution<int> duration{1, opts.max_duration};
        std::uniform_int_distribution<int> demand{0, opts.max_demand};
        std::uniform_real_distribution<double> unit{0.0, 1.0};

        inst.durations.reserve(opts.n_tasks);
        for (int i = 0; i < opts.n_tasks; ++i)
            inst.durations.push_back(gcs::Integer{duration(rng)});

        inst.capacities.assign(opts.n_resources, gcs::Integer{opts.capacity});
        inst.demands.assign(opts.n_resources, std::vector<gcs::Integer>(opts.n_tasks, gcs::Integer{0}));
        for (int r = 0; r < opts.n_resources; ++r)
            for (int i = 0; i < opts.n_tasks; ++i)
                inst.demands[r][i] = gcs::Integer{demand(rng)};

        for (int j = 1; j < opts.n_tasks; ++j)
            for (int i = std::max(0, j - opts.precedence_window); i < j; ++i)
                if (unit(rng) < opts.precedence_density)
                    inst.precedences.emplace_back(i, j);

        for (int i = 0; i < opts.n_tasks; ++i)
            if (unit(rng) < opts.machine_fraction)
                inst.machine_tasks.push_back(i);

        return inst;
    }

    /// Earliest start time of each task considering precedences alone: the
    /// length of the longest chain of durations ending just before it. A valid
    /// lower bound on the task's start in any feasible schedule, because the
    /// resources can only push a task later.
    [[nodiscard]] inline auto earliest_starts(const Instance & inst) -> std::vector<long long>
    {
        std::vector<std::vector<int>> preds(inst.n_tasks);
        for (const auto & [i, j] : inst.precedences)
            preds[j].push_back(i);

        std::vector<long long> est(inst.n_tasks, 0);
        for (int j = 0; j < inst.n_tasks; ++j)
            for (auto & i : preds[j])
                est[j] = std::max(est[j], est[i] + inst.durations[i].raw_value);
        return est;
    }

    /// Tail of each task considering precedences alone: the length of the
    /// longest chain of durations that must run strictly after it finishes. In
    /// any schedule of makespan H, task i cannot start after H - d_i - tail_i.
    [[nodiscard]] inline auto tails(const Instance & inst) -> std::vector<long long>
    {
        std::vector<std::vector<int>> succs(inst.n_tasks);
        for (const auto & [i, j] : inst.precedences)
            succs[i].push_back(j);

        std::vector<long long> tail(inst.n_tasks, 0);
        for (int i = inst.n_tasks - 1; i >= 0; --i)
            for (auto & j : succs[i])
                tail[i] = std::max(tail[i], inst.durations[j].raw_value + tail[j]);
        return tail;
    }

    /// The critical path length: a lower bound on the makespan from the
    /// precedences alone.
    [[nodiscard]] inline auto critical_path_length(const Instance & inst) -> long long
    {
        auto est = earliest_starts(inst);
        auto tail = tails(inst);
        long long cp = 0;
        for (int i = 0; i < inst.n_tasks; ++i)
            cp = std::max(cp, est[i] + inst.durations[i].raw_value + tail[i]);
        return cp;
    }

    /// Check a schedule against every constraint of the instance, from
    /// scratch. This is deliberately a separate, dumb, time-indexed
    /// implementation rather than anything shared with serial_schedule(): it is
    /// what makes it safe to shrink the model's horizon down to a heuristic
    /// schedule's makespan.
    [[nodiscard]] inline auto is_feasible(const Instance & inst, const std::vector<long long> & starts) -> bool
    {
        if (static_cast<int>(starts.size()) != inst.n_tasks)
            return false;

        long long horizon = 0;
        for (int i = 0; i < inst.n_tasks; ++i) {
            if (starts[i] < 0)
                return false;
            horizon = std::max(horizon, starts[i] + inst.durations[i].raw_value);
        }

        for (const auto & [i, j] : inst.precedences)
            if (starts[i] + inst.durations[i].raw_value > starts[j])
                return false;

        for (std::size_t r = 0; r < inst.capacities.size(); ++r) {
            std::vector<long long> load(horizon, 0);
            for (int i = 0; i < inst.n_tasks; ++i)
                for (auto t = starts[i]; t < starts[i] + inst.durations[i].raw_value; ++t)
                    load[t] += inst.demands[r][i].raw_value;
            for (auto & l : load)
                if (l > inst.capacities[r].raw_value)
                    return false;
        }

        std::vector<int> busy(horizon, 0);
        for (auto & i : inst.machine_tasks)
            for (auto t = starts[i]; t < starts[i] + inst.durations[i].raw_value; ++t)
                if (busy[t]++)
                    return false;

        return true;
    }

    /// A serial schedule generation scheme: take the tasks in index order
    /// (which is a topological order) and give each the earliest start that
    /// respects its predecessors, the resource capacities and the machine.
    /// The result is a feasible schedule, so its makespan is an upper bound on
    /// the optimal makespan, and hence a horizon the model can use without
    /// losing any optimal solution. The caller is expected to run it through
    /// is_feasible() before trusting it.
    [[nodiscard]] inline auto serial_schedule(const Instance & inst) -> std::vector<long long>
    {
        // Scheduling every task one after another is always feasible, so no
        // task is ever placed beyond this point, and the profile arrays below
        // are big enough.
        long long total = 0;
        for (auto & d : inst.durations)
            total += d.raw_value;

        std::vector<std::vector<long long>> load(inst.capacities.size(), std::vector<long long>(total, 0));
        std::vector<int> busy(total, 0);
        std::vector<char> needs_machine(inst.n_tasks, 0);
        for (auto & i : inst.machine_tasks)
            needs_machine[i] = 1;

        std::vector<std::vector<int>> preds(inst.n_tasks);
        for (const auto & [i, j] : inst.precedences)
            preds[j].push_back(i);

        std::vector<long long> start(inst.n_tasks, 0);
        for (int i = 0; i < inst.n_tasks; ++i) {
            auto len = inst.durations[i].raw_value;
            long long t = 0;
            for (auto & p : preds[i])
                t = std::max(t, start[p] + inst.durations[p].raw_value);

            for (;; ++t) {
                if (t + len > total)
                    throw std::logic_error{"serial schedule ran off the end of the horizon"};
                bool fits = true;
                for (std::size_t r = 0; fits && r < inst.capacities.size(); ++r)
                    for (auto u = t; u < t + len; ++u)
                        if (load[r][u] + inst.demands[r][i].raw_value > inst.capacities[r].raw_value) {
                            fits = false;
                            break;
                        }
                if (fits && needs_machine[i])
                    for (auto u = t; u < t + len; ++u)
                        if (busy[u]) {
                            fits = false;
                            break;
                        }
                if (fits)
                    break;
            }

            for (std::size_t r = 0; r < inst.capacities.size(); ++r)
                for (auto u = t; u < t + len; ++u)
                    load[r][u] += inst.demands[r][i].raw_value;
            if (needs_machine[i])
                for (auto u = t; u < t + len; ++u)
                    busy[u] = 1;
            start[i] = t;
        }

        return start;
    }

    /// The makespan of a schedule.
    [[nodiscard]] inline auto makespan_of(const Instance & inst, const std::vector<long long> & starts) -> long long
    {
        long long m = 0;
        for (int i = 0; i < inst.n_tasks; ++i)
            m = std::max(m, starts[i] + inst.durations[i].raw_value);
        return m;
    }
}

#endif
