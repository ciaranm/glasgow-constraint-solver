#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_RCPSP_INSTANCE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_RCPSP_INSTANCE_HH

// Instance model, random generator, .sch / .dzn / job-shop readers and schedule
// utilities for the RCPSP example. Kept separate from the model itself
// (rcpsp.cc) so that the model file reads as a model.
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
//
// \par Generalised time lags (RCPSP/max)
//
// Beyond the plain finish-to-start precedences, an instance may carry a list of
// generalised precedence relations, each `S_from + d <= S_to` for an arbitrary
// integer d. A non-negative d is a *minimum* time lag; a negative one is a
// *maximum* time lag, which is a backward arc, so the network of lags may have
// cycles. That is what makes the problem RCPSP/max rather than plain RCPSP, and
// it changes what the horizon machinery can promise --- see default_horizon().
//
// \par Job shops
//
// A job-shop instance is an RCPSP instance and needs no separate model: each
// machine is a renewable resource of capacity one, each operation demands one
// unit of the machine it runs on and none of any other, and each job is a chain
// of precedences. read_jss_stream() below is the whole of the support, and
// `--unary disjunctive` is what turns those capacity-one resources into
// Disjunctives.
//
// A plain RCPSP instance has an empty lag list, and everything below then
// behaves exactly as it did before generalised lags existed. That is deliberate:
// this example is part of the proof benchmark set (issues #632, #633), and the
// default instance family, horizon and posting order have to stay put.

#include <examples/dzn.hh>

#include <gcs/integer.hh>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <istream>
#include <limits>
#include <optional>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace rcpsp
{
    /// One generalised precedence relation: `S_from + d <= S_to`. A non-negative
    /// d is a minimum time lag, a negative d a maximum time lag.
    struct Lag
    {
        int from;
        int to;
        gcs::Integer d;
    };

    /// One execution mode of an activity: how long it takes, and what it needs
    /// of each renewable and each non-renewable resource while it does. A
    /// renewable demand is a rate, held for the whole duration; a non-renewable
    /// one is a lump drawn once from a project-wide budget.
    struct Mode
    {
        gcs::Integer duration;

        /// One per renewable resource, in the same order as Instance::capacities.
        std::vector<gcs::Integer> demands;

        /// One per non-renewable resource, in the same order as
        /// Instance::nonrenewable_capacities.
        std::vector<gcs::Integer> nonrenewable;
    };

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

        /// Generalised time lags, over and above the plain precedences above.
        /// Empty unless the instance came from a .sch file or was generated with
        /// a non-zero maximum-lag density, and everything that special-cases
        /// RCPSP/max keys off that emptiness rather than off a flag.
        std::vector<Lag> lags;

        /// The tasks that also need the single unary machine, ascending.
        std::vector<int> machine_tasks;

        /// modes[i] is task i's execution modes, in file order. **Empty unless
        /// the instance is multi-mode**, and everything that special-cases
        /// multi-mode keys off that emptiness rather than off a flag, exactly
        /// as `lags` does for RCPSP/max. When it is non-empty there is one
        /// entry per task and every entry has at least one mode.
        ///
        /// `durations[i]` and `demands[r][i]` then hold the *smallest* figure
        /// over modes[i]. That is what keeps earliest_starts(), tails() and
        /// critical_path_length() valid: they are lower bounds, and the
        /// smallest duration is the only one every mode selection admits.
        /// Anything wanting an upper bound has to ask max_durations().
        std::vector<std::vector<Mode>> modes;

        /// Capacity of each non-renewable resource: a budget drawn on once by
        /// each activity and spent over the whole project, rather than a rate
        /// held at each time point. Only a multi-mode instance has any, and
        /// they are what makes choosing the modes a problem in its own right
        /// rather than "give every activity its shortest mode".
        std::vector<gcs::Integer> nonrenewable_capacities;

        /// The task, if any, pinned to time zero. Set for a .sch instance, whose
        /// format carries a dummy source; left unset for a generated one, where
        /// minimising the makespan pins the schedule anyway.
        std::optional<int> source_task;

        std::string description;
    };

    /// Whether this instance has any maximum time lag, i.e. any backward arc.
    /// The horizon machinery below can promise rather less when it does.
    [[nodiscard]] inline auto has_maximum_lags(const Instance & inst) -> bool
    {
        for (const auto & l : inst.lags)
            if (l.d < gcs::Integer{0})
                return true;
        return false;
    }

    /// Whether this instance gives its activities a choice of execution mode.
    [[nodiscard]] inline auto is_multi_mode(const Instance & inst) -> bool
    {
        return ! inst.modes.empty();
    }

    /// The longest each task can take, over the modes it may be run in. On a
    /// single-mode instance this is just the durations.
    [[nodiscard]] inline auto max_durations(const Instance & inst) -> std::vector<gcs::Integer>
    {
        if (! is_multi_mode(inst))
            return inst.durations;

        std::vector<gcs::Integer> longest;
        longest.reserve(inst.modes.size());
        for (const auto & task_modes : inst.modes) {
            auto d = task_modes.front().duration;
            for (const auto & m : task_modes)
                d = std::max(d, m.duration);
            longest.push_back(d);
        }
        return longest;
    }

    /// A horizon for a multi-mode instance: run every activity in its longest
    /// mode, one after another. That is feasible for the *precedences and the
    /// renewable resources* whatever modes are chosen, so it is a genuine upper
    /// bound on the optimal makespan of any mode selection.
    ///
    /// It does not depend on finding a mode selection the non-renewable budgets
    /// allow, which is why this is used rather than a greedy schedule: deciding
    /// whether any such selection exists is itself NP-hard, so a greedy that
    /// went looking for one could not be trusted to have found the best it
    /// could, and one that ignored the budgets would not be a schedule.
    [[nodiscard]] inline auto multi_mode_horizon(const Instance & inst) -> long long
    {
        long long total = 0;
        for (const auto & d : max_durations(inst))
            total += d.raw_value;
        return total;
    }

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

        /// \name Maximum time lags, off by default
        ///
        /// A maximum lag is laid on top of the *longest path* of the precedence
        /// DAG between a pair, so the cycle it closes has weight exactly
        /// max_lag_slack: zero is tight, small is near-tight. With `infeasible`
        /// set, one of them is tightened to -1 instead, closing a negative cycle
        /// that no single constraint is violated by.
        ///
        /// These are generated in a stage that runs *after* every other draw
        /// from the RNG, and that stage is skipped entirely when
        /// max_lag_density is zero and infeasible is unset. That is what keeps
        /// every pre-existing --size/--seed instance bit-for-bit identical: the
        /// default settings below consume no random numbers at all.
        /// @{
        double max_lag_density = 0.0;
        int max_lag_span = 6;
        long long max_lag_slack = 2;
        bool infeasible = false;
        /// @}
    };

    namespace detail
    {
        constexpr long long unreachable = std::numeric_limits<long long>::min();

        /// Longest path weights in the precedence DAG, by dynamic programming
        /// over the topological order --- which is index order, because
        /// generate() only ever emits precedences with i < j. Entry (i, j) is
        /// the longest path from i to j, or `unreachable` if there is none. An
        /// edge (i, j) has weight durations[i], a precedence being
        /// finish-to-start, so the longest path from i to j is exactly the
        /// smallest value S_j - S_i can take once the precedences are enforced.
        [[nodiscard]] inline auto longest_paths(const Instance & inst) -> std::vector<std::vector<long long>>
        {
            auto n = static_cast<std::size_t>(inst.n_tasks);
            std::vector<std::vector<std::pair<int, long long>>> succ(n);
            for (const auto & [i, j] : inst.precedences)
                succ[static_cast<std::size_t>(i)].emplace_back(j, inst.durations[static_cast<std::size_t>(i)].raw_value);

            std::vector<std::vector<long long>> lp(n, std::vector<long long>(n, unreachable));
            for (auto ui = n; ui-- > 0;) {
                lp[ui][ui] = 0;
                for (const auto & [j, w] : succ[ui]) {
                    auto uj = static_cast<std::size_t>(j);
                    for (auto ut = uj; ut < n; ++ut) {
                        auto via = lp[uj][ut];
                        if (via != unreachable && w + via > lp[ui][ut])
                            lp[ui][ut] = w + via;
                    }
                }
            }
            return lp;
        }
    }

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

        // Maximum time lags, last, so that when they are switched off this
        // function draws exactly the random numbers it drew before they existed
        // and every previously-generated instance is reproduced bit for bit.
        if (opts.max_lag_density > 0.0 || opts.infeasible) {
            auto lp = detail::longest_paths(inst);

            // A pair can carry a maximum lag only if a precedence path already
            // joins it: the lag is expressed relative to that path's length.
            std::vector<std::pair<int, int>> candidates;
            for (int i = 0; i + 1 < opts.n_tasks; ++i)
                for (int j = i + 1; j <= std::min(opts.n_tasks - 1, i + opts.max_lag_span); ++j)
                    if (lp[static_cast<std::size_t>(i)][static_cast<std::size_t>(j)] != detail::unreachable)
                        candidates.emplace_back(i, j);

            std::vector<std::size_t> chosen;
            for (std::size_t c = 0; c != candidates.size(); ++c)
                if (unit(rng) < opts.max_lag_density)
                    chosen.push_back(c);

            // The one tightened past its longest path, when asked for: the pair
            // with the longest path, so the negative cycle it closes runs
            // through as many edges as possible.
            std::size_t tighten = chosen.size();
            if (opts.infeasible) {
                if (chosen.empty()) {
                    if (candidates.empty())
                        throw std::runtime_error{"--infeasible needs at least one pair joined by a precedence path; raise --density"};
                    chosen.push_back(candidates.size() / 2);
                }
                long long best = detail::unreachable;
                for (std::size_t idx = 0; idx != chosen.size(); ++idx) {
                    auto [i, j] = candidates[chosen[idx]];
                    auto w = lp[static_cast<std::size_t>(i)][static_cast<std::size_t>(j)];
                    if (w > best) {
                        best = w;
                        tighten = idx;
                    }
                }
            }

            for (std::size_t idx = 0; idx != chosen.size(); ++idx) {
                auto [i, j] = candidates[chosen[idx]];
                auto slack = (idx == tighten) ? -1LL : opts.max_lag_slack;
                auto bound = lp[static_cast<std::size_t>(i)][static_cast<std::size_t>(j)] + slack;
                // S_j - S_i <= bound, as the backward arc S_j + (-bound) <= S_i.
                inst.lags.push_back(Lag{j, i, gcs::Integer{-bound}});
            }

            inst.description += " max-lags=" + std::to_string(inst.lags.size()) + " max-lag-slack=" + std::to_string(opts.max_lag_slack) +
                (opts.infeasible ? " infeasible" : "");
        }

        return inst;
    }

    /// Earliest start time of each task considering precedences alone: the
    /// length of the longest chain of durations ending just before it. A valid
    /// lower bound on the task's start in any feasible schedule, because the
    /// resources can only push a task later.
    [[nodiscard]] inline auto earliest_starts(const Instance & inst) -> std::vector<long long>
    {
        std::vector<std::vector<int>> preds(static_cast<std::size_t>(inst.n_tasks));
        for (const auto & [i, j] : inst.precedences)
            preds[static_cast<std::size_t>(j)].push_back(i);

        std::vector<long long> est(static_cast<std::size_t>(inst.n_tasks), 0);
        for (std::size_t j = 0; j < est.size(); ++j)
            for (auto & i : preds[j])
                est[j] = std::max(est[j], est[static_cast<std::size_t>(i)] + inst.durations[static_cast<std::size_t>(i)].raw_value);
        return est;
    }

    /// Tail of each task considering precedences alone: the length of the
    /// longest chain of durations that must run strictly after it finishes. In
    /// any schedule of makespan H, task i cannot start after H - d_i - tail_i.
    [[nodiscard]] inline auto tails(const Instance & inst) -> std::vector<long long>
    {
        std::vector<std::vector<int>> succs(static_cast<std::size_t>(inst.n_tasks));
        for (const auto & [i, j] : inst.precedences)
            succs[static_cast<std::size_t>(i)].push_back(j);

        std::vector<long long> tail(static_cast<std::size_t>(inst.n_tasks), 0);
        for (auto i = tail.size(); i-- > 0;)
            for (auto & j : succs[i]) {
                auto uj = static_cast<std::size_t>(j);
                tail[i] = std::max(tail[i], inst.durations[uj].raw_value + tail[uj]);
            }
        return tail;
    }

    /// The critical path length: a lower bound on the makespan from the
    /// precedences alone.
    [[nodiscard]] inline auto critical_path_length(const Instance & inst) -> long long
    {
        auto est = earliest_starts(inst);
        auto tail = tails(inst);
        long long cp = 0;
        for (std::size_t i = 0; i < est.size(); ++i)
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
        for (std::size_t i = 0; i < starts.size(); ++i) {
            if (starts[i] < 0)
                return false;
            horizon = std::max(horizon, starts[i] + inst.durations[i].raw_value);
        }

        for (const auto & [i, j] : inst.precedences) {
            auto ui = static_cast<std::size_t>(i);
            if (starts[ui] + inst.durations[ui].raw_value > starts[static_cast<std::size_t>(j)])
                return false;
        }

        // The generalised lags too, minimum and maximum alike. This is what lets
        // the caller keep using a heuristic schedule's makespan as the horizon on
        // an RCPSP/max instance: serial_schedule() does not know about lags, so a
        // schedule that violates one is caught here and the caller falls back.
        for (const auto & l : inst.lags)
            if (starts[static_cast<std::size_t>(l.from)] + l.d.raw_value > starts[static_cast<std::size_t>(l.to)])
                return false;

        if (inst.source_task && starts[static_cast<std::size_t>(*inst.source_task)] != 0)
            return false;

        for (std::size_t r = 0; r < inst.capacities.size(); ++r) {
            std::vector<long long> load(horizon, 0);
            for (std::size_t i = 0; i < starts.size(); ++i)
                for (auto t = starts[i]; t < starts[i] + inst.durations[i].raw_value; ++t)
                    load[t] += inst.demands[r][i].raw_value;
            for (auto & l : load)
                if (l > inst.capacities[r].raw_value)
                    return false;
        }

        std::vector<int> busy(horizon, 0);
        for (auto & m : inst.machine_tasks) {
            auto i = static_cast<std::size_t>(m);
            for (auto t = starts[i]; t < starts[i] + inst.durations[i].raw_value; ++t)
                if (busy[t]++)
                    return false;
        }

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
        std::vector<char> needs_machine(static_cast<std::size_t>(inst.n_tasks), 0);
        for (auto & i : inst.machine_tasks)
            needs_machine[static_cast<std::size_t>(i)] = 1;

        std::vector<std::vector<int>> preds(static_cast<std::size_t>(inst.n_tasks));
        for (const auto & [i, j] : inst.precedences)
            preds[static_cast<std::size_t>(j)].push_back(i);

        std::vector<long long> start(static_cast<std::size_t>(inst.n_tasks), 0);
        for (std::size_t i = 0; i < start.size(); ++i) {
            auto len = inst.durations[i].raw_value;
            long long t = 0;
            for (auto & p : preds[i]) {
                auto up = static_cast<std::size_t>(p);
                t = std::max(t, start[up] + inst.durations[up].raw_value);
            }

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
        for (std::size_t i = 0; i < starts.size(); ++i)
            m = std::max(m, starts[i] + inst.durations[i].raw_value);
        return m;
    }

    /// The fallback horizon, for when no feasible schedule is to hand:
    /// `sum_i max(p_i, largest outgoing minimum lag from i)`. This is the
    /// standard RCPSP/max planning horizon (Bartusch, Moehring and
    /// Radermacher), and on an instance with no generalised lags it collapses
    /// to the sum of the durations, which is the makespan of scheduling
    /// everything one task after another.
    ///
    /// \warning On a plain RCPSP instance this is a genuine upper bound on the
    /// optimal makespan, because the serial schedule it measures is feasible.
    /// With *maximum* lags it is not a proof of anything --- RCPSP/max
    /// feasibility is NP-hard, and a serial schedule may violate a maximum lag.
    /// It is a modelling horizon there, and --horizon overrides it. The model
    /// only reaches for this when serial_schedule() failed is_feasible(), so on
    /// a plain instance the horizon still rests on a checked feasible schedule.
    [[nodiscard]] inline auto default_horizon(const Instance & inst) -> long long
    {
        std::vector<long long> per_task(static_cast<std::size_t>(inst.n_tasks), 0);
        for (std::size_t i = 0; i < per_task.size(); ++i)
            per_task[i] = inst.durations[i].raw_value;

        // A precedence's own weight is the tail's duration, so it never raises
        // the term above; only a generalised minimum lag can.
        for (const auto & l : inst.lags)
            if (l.d.raw_value > per_task[static_cast<std::size_t>(l.from)])
                per_task[static_cast<std::size_t>(l.from)] = l.d.raw_value;

        long long total = 0;
        for (const auto & v : per_task)
            total += v;
        return total;
    }

    /// Read a single-mode RCPSP/max instance in ProGen/max `.sch` format, the
    /// format the standard UBO, CD (testsetc / testsetd) and SM (sm_j10, sm_j20,
    /// sm_j30) sets are distributed in.
    ///
    /// The layout, for `n` real activities and `g` renewable resources, is
    /// `1 + (n + 2) + (n + 2) + 1` whitespace-separated lines:
    ///
    ///     n  g  0  0                                            header
    ///     i  1  s_i  j_1 .. j_{s_i}  [d_1] .. [d_{s_i}]         n + 2 lines
    ///     i  1  p_i  r_i1 .. r_ig                               n + 2 lines
    ///     R_1 .. R_g                                            capacities
    ///
    /// Activity `0` is a dummy source and activity `n + 1` a dummy sink, both of
    /// zero duration and zero demand, so the file describes `n + 2` activities in
    /// total and that is what the Instance ends up holding. The `1` in the second
    /// column is a mode count: this reader handles single-mode instances only and
    /// rejects anything else, because a multi-mode file puts
    /// `|modes(i)| x |modes(j)|` weights in each bracket group and the line layout
    /// changes.
    ///
    /// The bracketed number after the successor list is the **arc weight**, and an
    /// arc `i -> j` of weight `d` means `S_j - S_i >= d`, i.e. `S_i + d <= S_j`,
    /// which is exactly this file's Lag. Brackets are pure delimiters. There is no
    /// min/max marking anywhere in the format: **the sign is the only signal**. A
    /// pair of opposite arcs `i -> j [a]` and `j -> i [-b]` says
    /// `a <= S_j - S_i <= b`, a minimum lag of `a` and a maximum lag of `b`; a lone
    /// negative arc is a bare maximum lag. The whole precedence block is therefore
    /// literally a difference-logic system, which is why every arc lands in
    /// `lags` rather than in `precedences`: the weights are start-to-start, not
    /// finish-to-start, and may be smaller than the tail's duration.
    ///
    /// The format was checked against real instances (`sm_j10/psp1.sch` and
    /// `ubo_*/psp1.sch` as distributed in the `or-tools/data` repository), against
    /// Schwindt's own ProGen/max input-format document for the consumer-producer
    /// variant, and against the SCIP (`reader_sch.c`) and or-tools
    /// (`rcpsp_parser.cc`) readers.
    [[nodiscard]] inline auto read_sch_stream(std::istream & in, const std::string & description) -> Instance
    {
        // The header line has to be read on its own: the resource-investment
        // variant of the format adds a fifth field, which a flat token stream
        // could not tell apart from the first activity's index.
        std::string header_line;
        while (std::getline(in, header_line))
            if (header_line.find_first_not_of(" \t\r\n") != std::string::npos)
                break;

        std::vector<long long> header;
        {
            std::istringstream hs{header_line};
            for (long long v; hs >> v;)
                header.push_back(v);
        }
        if (header.size() < 2)
            throw std::runtime_error{"not a ProGen/max .sch file: the header needs at least an activity and a resource count"};
        if (header.size() > 4)
            throw std::runtime_error{"unsupported .sch variant: a header of more than four fields is the resource-investment format"};
        if (header.size() >= 3 && header[2] != 0)
            throw std::runtime_error{"unsupported .sch instance: non-renewable resources are not modelled here"};
        if (header.size() >= 4 && header[3] != 0)
            throw std::runtime_error{"unsupported .sch instance: doubly-constrained resources are not modelled here"};

        auto real_activities = header[0];
        auto resources = header[1];
        if (real_activities <= 0 || real_activities > 1000000 || resources < 0 || resources > 1000000)
            throw std::runtime_error{"not a ProGen/max .sch file: implausible activity or resource count"};

        // Everything after the header is a flat token stream once the brackets
        // are turned into whitespace, because each successor count says exactly
        // how many ids and how many weights follow it.
        std::ostringstream rest;
        for (std::string line; std::getline(in, line);) {
            for (auto & c : line)
                if (c == '[' || c == ']')
                    c = ' ';
            rest << line << '\n';
        }
        std::istringstream nums{rest.str()};

        auto next = [&](const char * what) -> long long {
            long long v = 0;
            if (! (nums >> v))
                throw std::runtime_error{std::string{"instance ended while reading "} + what};
            return v;
        };

        Instance inst;
        inst.description = description;
        inst.n_tasks = static_cast<int>(real_activities) + 2;
        inst.source_task = 0;

        auto un = static_cast<std::size_t>(inst.n_tasks), um = static_cast<std::size_t>(resources);

        auto read_index_and_modes = [&](std::size_t expected, const char * what) {
            auto idx = next(what);
            if (idx != static_cast<long long>(expected))
                throw std::runtime_error{"malformed .sch file: activity records are out of order"};
            if (next("a mode count") != 1)
                throw std::runtime_error{"unsupported .sch instance: only single-mode instances are handled"};
        };

        for (std::size_t i = 0; i != un; ++i) {
            read_index_and_modes(i, "an activity index in the precedence block");
            auto successors = next("a successor count");
            if (successors < 0 || successors > static_cast<long long>(un))
                throw std::runtime_error{"malformed .sch file: implausible successor count"};
            std::vector<int> targets;
            targets.reserve(static_cast<std::size_t>(successors));
            for (long long s = 0; s != successors; ++s)
                targets.push_back(static_cast<int>(next("a successor index")));
            for (long long s = 0; s != successors; ++s)
                inst.lags.push_back(Lag{static_cast<int>(i), targets[static_cast<std::size_t>(s)], gcs::Integer{next("an arc weight")}});
        }

        inst.durations.reserve(un);
        inst.demands.assign(um, std::vector<gcs::Integer>(un, gcs::Integer{0}));
        for (std::size_t i = 0; i != un; ++i) {
            read_index_and_modes(i, "an activity index in the demand block");
            inst.durations.push_back(gcs::Integer{next("a duration")});
            for (std::size_t k = 0; k != um; ++k)
                inst.demands[k][i] = gcs::Integer{next("a demand")};
        }

        inst.capacities.reserve(um);
        for (std::size_t k = 0; k != um; ++k)
            inst.capacities.push_back(gcs::Integer{next("a capacity")});

        for (const auto & l : inst.lags)
            if (l.from < 0 || l.from >= inst.n_tasks || l.to < 0 || l.to >= inst.n_tasks)
                throw std::runtime_error{"malformed .sch file: a time lag refers to a nonexistent activity"};
        for (const auto & p : inst.durations)
            if (p < gcs::Integer{0})
                throw std::runtime_error{"malformed .sch file: a negative duration"};
        for (const auto & c : inst.capacities)
            if (c < gcs::Integer{0})
                throw std::runtime_error{"malformed .sch file: a negative capacity"};

        return inst;
    }

    /// Read a multi-mode RCPSP instance in the PSPLIB `.mm` format, the one the
    /// `j10`, `j12`, `j14`, `j16`, `j18`, `j20` and `j30` multi-mode sets are
    /// distributed in.
    ///
    /// The file is a sequence of `****`-separated sections. Three are read: the
    /// resource counts, `PRECEDENCE RELATIONS:` (one line per job, giving its
    /// mode count and its one-based successors) and `REQUESTS/DURATIONS:` (one
    /// line per *mode*, giving its duration and its demand on each renewable and
    /// each non-renewable resource, with the job number written only on the
    /// first of a job's modes). `RESOURCEAVAILABILITIES:` closes it with one
    /// capacity per resource, renewables first. Job 1 is a dummy source and job
    /// n a dummy sink, both single-mode and of zero duration.
    ///
    /// \par What multi-mode adds, and why it is the point
    ///
    /// An activity chooses one of several modes, and the mode fixes both how
    /// long it runs and how much of each resource it takes while it does. So a
    /// task's duration and its demands are **decisions**, not data --- which is
    /// exactly the case #748 and #749 taught `Cumulative` to reason about, and
    /// the case no single-mode instance can exercise. A shorter mode generally
    /// costs more of some resource, so the trade-off is real.
    ///
    /// **Non-renewable resources** are what stop the answer being "give every
    /// activity its shortest mode". A renewable resource is a rate, capped at
    /// each time point, and is what a `Cumulative` says; a non-renewable one is
    /// a lump sum drawn once per activity from a project-wide budget, and is one
    /// linear inequality over the whole instance. Without them the mode choice
    /// would decompose and the instance would be a plain RCPSP with extra steps.
    ///
    /// \par Modes that cannot run
    ///
    /// A mode whose renewable demand exceeds that resource's capacity, or whose
    /// non-renewable demand exceeds that budget on its own, can never be
    /// selected in any feasible schedule, so it is dropped as the file is read.
    /// This is what the literature does and it keeps the mode variables' domains
    /// honest. An activity all of whose modes go that way makes the instance
    /// infeasible for a reason that has nothing to do with scheduling, and is
    /// reported as a malformed instance rather than passed on to the solver.
    [[nodiscard]] inline auto read_mm_stream(std::istream & in, const std::string & description) -> Instance
    {
        std::vector<std::string> lines;
        for (std::string line; std::getline(in, line);)
            lines.push_back(line);

        // A data line in this format is digits, space and sign and nothing
        // else. That is what tells the numbers apart from the column headings
        // and the rows of dashes that sit above them, without this reader having
        // to know how many heading lines each section has: a row of dashes
        // carries no digit, so it is not a data line whether or not a sign is
        // allowed in one.
        //
        // Signs are allowed here precisely so that a file with a negative
        // duration in it is *read* and then rejected by the check that says so.
        // Treating that line as a heading instead would skip it, shift every
        // number after it by one, and report whatever the shifted stream
        // happened to violate first.
        auto numeric_line = [](const std::string & line) {
            bool any_digit = false;
            for (auto & c : line) {
                if (c >= '0' && c <= '9')
                    any_digit = true;
                else if (c != ' ' && c != '\t' && c != '\r' && c != '-' && c != '+')
                    return false;
            }
            return any_digit;
        };

        // The integer at the end of a `name : value` line, which is how the
        // counts at the top of the file are written.
        auto field = [&](const std::string & name) -> long long {
            for (const auto & line : lines) {
                auto at = line.find(name);
                if (at == std::string::npos)
                    continue;
                auto colon = line.find(':', at);
                if (colon == std::string::npos)
                    continue;
                std::istringstream vs{line.substr(colon + 1)};
                long long v = 0;
                if (vs >> v)
                    return v;
            }
            throw std::runtime_error{"not a PSPLIB .mm file: no '" + name + "' line"};
        };

        // Every number in the section a marker opens, up to the `****` that
        // closes it.
        auto section = [&](const std::string & marker) -> std::vector<long long> {
            std::size_t at = 0;
            while (at != lines.size() && lines[at].find(marker) == std::string::npos)
                ++at;
            if (at == lines.size())
                throw std::runtime_error{"not a PSPLIB .mm file: no '" + marker + "' section"};

            std::vector<long long> out;
            for (++at; at != lines.size() && lines[at].find("***") == std::string::npos; ++at) {
                if (! numeric_line(lines[at]))
                    continue;
                std::istringstream ls{lines[at]};
                for (long long v; ls >> v;)
                    out.push_back(v);
            }
            return out;
        };

        auto n_tasks = field("jobs (incl. supersource/sink )");
        auto n_renewable = field("- renewable");
        auto n_nonrenewable = field("- nonrenewable");
        if (field("- doubly constrained") != 0)
            throw std::runtime_error{"unsupported .mm instance: doubly-constrained resources are not modelled here"};
        if (n_tasks < 2 || n_tasks > 1000000)
            throw std::runtime_error{"not a PSPLIB .mm file: implausible job count"};
        if (n_renewable < 0 || n_nonrenewable < 0 || n_renewable > 1000 || n_nonrenewable > 1000)
            throw std::runtime_error{"not a PSPLIB .mm file: implausible resource count"};

        Instance inst;
        inst.n_tasks = static_cast<int>(n_tasks);
        auto un = static_cast<std::size_t>(n_tasks);
        auto ur = static_cast<std::size_t>(n_renewable), uk = static_cast<std::size_t>(n_nonrenewable);

        // A cursor over a section's numbers, so that a file which ends early
        // says so rather than reading zeroes.
        struct Cursor
        {
            const std::vector<long long> & vals;
            std::size_t at = 0;
            const char * what;
            auto next() -> long long
            {
                if (at == vals.size())
                    throw std::runtime_error{std::string{"malformed .mm file: the "} + what + " section ended early"};
                return vals[at++];
            }
        };

        auto precedence_vals = section("PRECEDENCE RELATIONS:");
        Cursor prec{precedence_vals, 0, "precedence"};
        std::vector<long long> mode_counts;
        mode_counts.reserve(un);
        for (std::size_t i = 0; i != un; ++i) {
            if (prec.next() != static_cast<long long>(i) + 1)
                throw std::runtime_error{"malformed .mm file: the precedence block's jobs are out of order"};
            auto n_modes = prec.next();
            if (n_modes < 1 || n_modes > 1000)
                throw std::runtime_error{"malformed .mm file: job " + std::to_string(i + 1) + " has an implausible mode count"};
            mode_counts.push_back(n_modes);

            auto n_successors = prec.next();
            if (n_successors < 0 || n_successors > static_cast<long long>(un))
                throw std::runtime_error{"malformed .mm file: job " + std::to_string(i + 1) + " has an implausible successor count"};
            for (long long s = 0; s != n_successors; ++s) {
                auto j = static_cast<int>(prec.next()) - 1;
                if (j < 0 || j >= inst.n_tasks)
                    throw std::runtime_error{"malformed .mm file: a precedence to a nonexistent job"};
                // earliest_starts(), tails() and longest_paths() all walk the
                // tasks in index order and need that to be topological. PSPLIB
                // numbers its jobs that way; a file that did not would give
                // silently wrong bounds rather than an error, so check it.
                if (j <= static_cast<int>(i))
                    throw std::runtime_error{"malformed .mm file: job " + std::to_string(j + 1) + " is a successor of job " + std::to_string(i + 1) +
                        ", so the jobs are not in topological order; this reader needs them to be"};
                inst.precedences.emplace_back(static_cast<int>(i), j);
            }
        }

        auto capacity_vals = section("RESOURCEAVAILABILITIES:");
        Cursor caps{capacity_vals, 0, "resource availabilities"};
        for (std::size_t r = 0; r != ur; ++r) {
            auto c = caps.next();
            if (c < 0)
                throw std::runtime_error{"malformed .mm file: a negative renewable capacity"};
            inst.capacities.push_back(gcs::Integer{c});
        }
        for (std::size_t k = 0; k != uk; ++k) {
            auto c = caps.next();
            if (c < 0)
                throw std::runtime_error{"malformed .mm file: a negative non-renewable capacity"};
            inst.nonrenewable_capacities.push_back(gcs::Integer{c});
        }

        // The job number is written only on the first of a job's modes, so the
        // records are not all the same width. Knowing each job's mode count from
        // the precedence block above is what makes a flat stream unambiguous.
        auto request_vals = section("REQUESTS/DURATIONS:");
        Cursor req{request_vals, 0, "requests/durations"};
        inst.modes.assign(un, {});
        for (std::size_t i = 0; i != un; ++i) {
            for (long long m = 0; m != mode_counts[i]; ++m) {
                if (m == 0 && req.next() != static_cast<long long>(i) + 1)
                    throw std::runtime_error{"malformed .mm file: the requests block's jobs are out of order"};
                if (req.next() != m + 1)
                    throw std::runtime_error{"malformed .mm file: job " + std::to_string(i + 1) + "'s modes are not numbered 1 upwards"};

                auto duration = req.next();
                if (duration < 0)
                    throw std::runtime_error{"malformed .mm file: job " + std::to_string(i + 1) + " has a negative duration"};
                Mode mode{gcs::Integer{duration}, {}, {}};

                bool possible = true;
                for (std::size_t r = 0; r != ur; ++r) {
                    auto d = req.next();
                    if (d < 0)
                        throw std::runtime_error{"malformed .mm file: a negative renewable demand"};
                    if (gcs::Integer{d} > inst.capacities[r])
                        possible = false;
                    mode.demands.push_back(gcs::Integer{d});
                }
                for (std::size_t k = 0; k != uk; ++k) {
                    auto d = req.next();
                    if (d < 0)
                        throw std::runtime_error{"malformed .mm file: a negative non-renewable demand"};
                    if (gcs::Integer{d} > inst.nonrenewable_capacities[k])
                        possible = false;
                    mode.nonrenewable.push_back(gcs::Integer{d});
                }

                if (possible)
                    inst.modes[i].push_back(std::move(mode));
            }

            if (inst.modes[i].empty())
                throw std::runtime_error{
                    "job " + std::to_string(i + 1) + " has no mode a resource capacity allows, so the instance is infeasible before any scheduling"};
        }

        // The smallest figure over the modes, which is what every bound derived
        // from `durations` and `demands` is allowed to assume. See Instance::modes.
        inst.durations.reserve(un);
        inst.demands.assign(ur, std::vector<gcs::Integer>(un, gcs::Integer{0}));
        for (std::size_t i = 0; i != un; ++i) {
            auto shortest = inst.modes[i].front().duration;
            for (const auto & m : inst.modes[i])
                shortest = std::min(shortest, m.duration);
            inst.durations.push_back(shortest);

            for (std::size_t r = 0; r != ur; ++r) {
                auto least = inst.modes[i].front().demands[r];
                for (const auto & m : inst.modes[i])
                    least = std::min(least, m.demands[r]);
                inst.demands[r][i] = least;
            }
        }

        std::size_t total_modes = 0;
        for (const auto & task_modes : inst.modes)
            total_modes += task_modes.size();
        inst.description = description + " n=" + std::to_string(inst.n_tasks) + " renewable=" + std::to_string(n_renewable) +
            " nonrenewable=" + std::to_string(n_nonrenewable) + " modes=" + std::to_string(total_modes);
        return inst;
    }

    [[nodiscard]] inline auto read_mm_file(const std::string & path) -> Instance
    {
        std::ifstream in{path};
        if (! in)
            throw std::runtime_error{"could not open instance file: " + path};
        return read_mm_stream(in, "mm " + path);
    }

    /// Read a job-shop scheduling instance in the standard OR-Library layout,
    /// the one the `ft`, `la`, `abz`, `orb`, `swv` and `ta` sets are distributed
    /// in.
    ///
    /// After any amount of leading blurb --- the bundled `jobshop1.txt` puts an
    /// `instance <name>` line and a free-text description between rows of `+`
    /// signs --- the file is
    ///
    ///     J  M                                   job count, machine count
    ///     m_1 p_1  m_2 p_2  ..  m_M p_M          one line per job
    ///
    /// where job `j` occupies machine `m_1` for `p_1` time units, then `m_2` for
    /// `p_2`, and so on. The pairs are in *processing order*, and the machine
    /// indices are zero-based and a permutation of `0..M-1`: every job visits
    /// every machine exactly once, which is what makes this a job shop rather
    /// than a general shop, and this reader insists on it rather than guessing
    /// what a repeated or missing machine was meant to mean.
    ///
    /// \par How a job shop lands in an RCPSP Instance
    ///
    /// Operations are numbered job-major --- job `j`'s `k`th operation is task
    /// `j * M + k` --- so index order is a topological order of the job chains,
    /// which earliest_starts(), tails() and longest_paths() all require. The
    /// chain itself is an ordinary finish-to-start precedence per consecutive
    /// pair, so there are no time lags and this is plain RCPSP, not RCPSP/max.
    ///
    /// A machine is a **capacity-one renewable resource** that its own
    /// operations demand one unit of and every other operation demands none of.
    /// That is not a re-modelling of the problem: it is what a machine is, and
    /// it is why rcpsp.cc needs no job-shop case at all. `--unary disjunctive`
    /// then posts one Disjunctive per machine over exactly that machine's
    /// operations, and the default `--unary cumulative` posts the capacity-one
    /// Cumulative saying the same thing, which is the control arm.
    ///
    /// \par What this is for
    ///
    /// Every RCPSP collection to hand has capacities of three and up, so none of
    /// them posts a Disjunctive at all, and the unary propagation rules have had
    /// no real instance family to be measured on. A job shop is that family: it
    /// is all unary machines, it is what the unary scheduling literature reports
    /// on, and the `la_x` RCPSP set is these instances with their capacities
    /// raised to two or three.
    ///
    /// Taillard's own distribution format is a different layout --- named header
    /// fields, then the durations and the machine assignments as two separate
    /// matrices --- and is not read here. A file holding several instances is
    /// not read here either: this takes the first one it finds.
    [[nodiscard]] inline auto read_jss_stream(std::istream & in, const std::string & description) -> Instance
    {
        // Leading blurb is anything that is not a row of numbers: the bundled
        // file's `instance <name>` line, its rows of `+` signs, and the prose
        // between them. The dimensions are the first line that is numeric
        // throughout, which no line of blurb is.
        auto numeric_line = [](const std::string & line) {
            bool any_digit = false;
            for (auto & c : line) {
                if (c >= '0' && c <= '9')
                    any_digit = true;
                else if (c != ' ' && c != '\t' && c != '\r')
                    return false;
            }
            return any_digit;
        };

        std::string dims_line;
        while (std::getline(in, dims_line))
            if (numeric_line(dims_line))
                break;

        long long n_jobs = 0, n_machines = 0;
        {
            std::istringstream ds{dims_line};
            long long extra = 0;
            if (! (ds >> n_jobs >> n_machines))
                throw std::runtime_error{"not a job-shop instance: no line giving a job count and a machine count"};
            if (ds >> extra)
                throw std::runtime_error{"not a job-shop instance: the first numeric line has more than a job count and a machine count"};
        }
        if (n_jobs < 1 || n_machines < 1 || n_jobs > 100000 || n_machines > 100000)
            throw std::runtime_error{"not a job-shop instance: implausible job or machine count"};
        // Bound the product too, not just the factors: the operation count is
        // what gets cast to int and what sizes every array below, and a header
        // of two plausible-looking factors can still ask for more operations
        // than an int holds.
        if (n_jobs * n_machines > 1000000)
            throw std::runtime_error{"not a job-shop instance: " + std::to_string(n_jobs) + " jobs of " + std::to_string(n_machines) +
                " operations each is more than this reader will build"};

        auto next = [&](const char * what) -> long long {
            long long v = 0;
            if (! (in >> v))
                throw std::runtime_error{std::string{"job-shop instance ended while reading "} + what};
            return v;
        };

        Instance inst;
        auto uj = static_cast<std::size_t>(n_jobs), um = static_cast<std::size_t>(n_machines);
        inst.n_tasks = static_cast<int>(n_jobs * n_machines);
        inst.durations.assign(static_cast<std::size_t>(inst.n_tasks), gcs::Integer{0});
        inst.capacities.assign(um, gcs::Integer{1});
        inst.demands.assign(um, std::vector<gcs::Integer>(static_cast<std::size_t>(inst.n_tasks), gcs::Integer{0}));

        for (std::size_t j = 0; j != uj; ++j) {
            std::vector<char> visited(um, 0);
            for (std::size_t k = 0; k != um; ++k) {
                auto machine = next("a machine index");
                auto duration = next("a duration");
                if (machine < 0 || machine >= n_machines)
                    throw std::runtime_error{"malformed job-shop instance: job " + std::to_string(j) + " names machine " + std::to_string(machine) +
                        ", which is outside 0.." + std::to_string(n_machines - 1)};
                if (duration < 0)
                    throw std::runtime_error{"malformed job-shop instance: job " + std::to_string(j) + " has a negative duration"};
                if (visited[static_cast<std::size_t>(machine)])
                    throw std::runtime_error{"malformed job-shop instance: job " + std::to_string(j) + " visits machine " + std::to_string(machine) +
                        " twice, so it is not a job shop as this reader understands one"};
                visited[static_cast<std::size_t>(machine)] = 1;

                auto task = j * um + k;
                inst.durations[task] = gcs::Integer{duration};
                inst.demands[static_cast<std::size_t>(machine)][task] = gcs::Integer{1};
                if (k > 0)
                    inst.precedences.emplace_back(static_cast<int>(task - 1), static_cast<int>(task));
            }
        }

        inst.description = description + " jobs=" + std::to_string(n_jobs) + " machines=" + std::to_string(n_machines) +
            " operations=" + std::to_string(inst.n_tasks);
        return inst;
    }

    [[nodiscard]] inline auto read_jss_file(const std::string & path) -> Instance
    {
        std::ifstream in{path};
        if (! in)
            throw std::runtime_error{"could not open instance file: " + path};
        return read_jss_stream(in, "jss " + path);
    }

    [[nodiscard]] inline auto read_file(const std::string & path) -> Instance
    {
        std::ifstream in{path};
        if (! in)
            throw std::runtime_error{"could not open instance file: " + path};
        return read_sch_stream(in, "file " + path);
    }

    /// Read a plain RCPSP instance in the MiniZinc data format that goes with
    /// the standard `rcpsp.mzn` model, as distributed in the MiniZinc
    /// benchmarks: the Pack, Pack_d, PSPLib (j30/j60/j120), la_x, ksd15_d and
    /// bl collections.
    ///
    /// The file defines `n_res`, the capacities `rc`, `n_tasks`, the durations
    /// `d`, the demands `rr` as a `[Res, Tasks]` matrix, and the successors
    /// `suc` as an array of sets of one-based task indices. RCPSP/max data files
    /// name the same things `rcap`, `dur` and `dcons` instead and carry time
    /// lags rather than precedences; those are a different format and belong in
    /// read_sch_stream, not here.
    ///
    /// This is plain RCPSP, so the instance comes back with no time lags, no
    /// machine tasks and no pinned source: `suc` is finish-to-start throughout.
    ///
    /// \warning Only the resource and precedence structure is read. The
    /// redundant pairwise non-overlap constraints that `rcpsp.mzn` itself posts
    /// are deliberately **not** reproduced --- they are a modelling choice of
    /// that file, not part of the instance, and posting them changes what a
    /// presolver looking for cross-resource conflicts has left to find.
    [[nodiscard]] inline auto read_dzn_file(const std::string & path) -> Instance
    {
        auto data = dzn::read(path);

        Instance inst;
        inst.n_tasks = static_cast<int>(data.integer("n_tasks"));
        auto n_res = static_cast<std::size_t>(data.integer("n_res"));
        if (inst.n_tasks < 1)
            throw std::runtime_error{"'" + path + "' has no tasks"};

        for (auto & c : data.integers("rc"))
            inst.capacities.push_back(gcs::Integer{c});
        if (inst.capacities.size() != n_res)
            throw std::runtime_error{
                "'" + path + "' gives " + std::to_string(inst.capacities.size()) + " capacities for " + std::to_string(n_res) + " resources"};

        for (auto & p : data.integers("d")) {
            if (p < 1)
                throw std::runtime_error{
                    "'" + path + "' has a task of duration " + std::to_string(p) + "; this model needs every duration to be at least one"};
            inst.durations.push_back(gcs::Integer{p});
        }
        if (static_cast<int>(inst.durations.size()) != inst.n_tasks)
            throw std::runtime_error{
                "'" + path + "' gives " + std::to_string(inst.durations.size()) + " durations for " + std::to_string(inst.n_tasks) + " tasks"};

        auto rr = data.matrix("rr");
        if (rr.size() != n_res)
            throw std::runtime_error{"'" + path + "' gives demands for " + std::to_string(rr.size()) + " resources, not " + std::to_string(n_res)};
        inst.demands.assign(n_res, std::vector<gcs::Integer>(static_cast<std::size_t>(inst.n_tasks), gcs::Integer{0}));
        for (std::size_t r = 0; r != n_res; ++r) {
            if (static_cast<int>(rr[r].size()) != inst.n_tasks)
                throw std::runtime_error{"'" + path + "' gives " + std::to_string(rr[r].size()) + " demands for resource " + std::to_string(r) +
                    ", not " + std::to_string(inst.n_tasks)};
            for (std::size_t i = 0; i != rr[r].size(); ++i) {
                if (rr[r][i] < 0)
                    throw std::runtime_error{"'" + path + "' has a negative demand"};
                inst.demands[r][i] = gcs::Integer{rr[r][i]};
            }
        }

        // `suc` is one-based, and every collection in the MiniZinc benchmarks
        // lists it in topological order. earliest_starts(), tails() and
        // longest_paths() all walk the tasks in index order and rely on that, so
        // a file that broke it would give silently wrong bounds rather than an
        // error --- hence the check rather than a sort.
        auto suc = data.sets("suc");
        if (static_cast<int>(suc.size()) != inst.n_tasks)
            throw std::runtime_error{
                "'" + path + "' gives successors for " + std::to_string(suc.size()) + " tasks, not " + std::to_string(inst.n_tasks)};
        for (std::size_t at = 0; at != suc.size(); ++at) {
            auto i = static_cast<int>(at);
            for (auto & one_based : suc[at]) {
                auto j = static_cast<int>(one_based) - 1;
                if (j < 0 || j >= inst.n_tasks)
                    throw std::runtime_error{"'" + path + "' has a precedence to a nonexistent task"};
                if (j <= i)
                    throw std::runtime_error{"'" + path + "' lists task " + std::to_string(one_based) + " as a successor of task " +
                        std::to_string(i + 1) + ", so the tasks are not in topological order; this reader needs them to be"};
                inst.precedences.emplace_back(i, j);
            }
        }

        inst.description = "dzn " + path + " n=" + std::to_string(inst.n_tasks) + " resources=" + std::to_string(n_res) +
            " precedences=" + std::to_string(inst.precedences.size());
        return inst;
    }
}

#endif
