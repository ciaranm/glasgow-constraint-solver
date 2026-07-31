#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_RCPSP_INSTANCE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_RCPSP_INSTANCE_HH

// Instance model, random generator, .sch reader and schedule utilities for the
// RCPSP example. Kept separate from the model itself (rcpsp.cc) so that the
// model file reads as a model.
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
// A plain RCPSP instance has an empty lag list, and everything below then
// behaves exactly as it did before generalised lags existed. That is deliberate:
// this example is part of the proof benchmark set (issues #632, #633), and the
// default instance family, horizon and posting order have to stay put.

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
            for (int i = inst.n_tasks - 1; i >= 0; --i) {
                auto ui = static_cast<std::size_t>(i);
                lp[ui][ui] = 0;
                for (const auto & [j, w] : succ[ui])
                    for (int t = j; t < inst.n_tasks; ++t) {
                        auto ut = static_cast<std::size_t>(t);
                        auto via = lp[static_cast<std::size_t>(j)][ut];
                        if (via != unreachable && w + via > lp[ui][ut])
                            lp[ui][ut] = w + via;
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
        for (int i = 0; i < inst.n_tasks; ++i)
            per_task[static_cast<std::size_t>(i)] = inst.durations[static_cast<std::size_t>(i)].raw_value;

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

    [[nodiscard]] inline auto read_file(const std::string & path) -> Instance
    {
        std::ifstream in{path};
        if (! in)
            throw std::runtime_error{"could not open instance file: " + path};
        return read_sch_stream(in, "file " + path);
    }
}

#endif
