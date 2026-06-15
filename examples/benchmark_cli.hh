#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_BENCHMARK_CLI_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_EXAMPLES_BENCHMARK_CLI_HH

// Shared helpers for the benchmark / example command-line programs: a dom-wdeg
// weighting-scheme name parser (for a `--branch` flag) and a graceful
// `--timeout` wrapper around solve_with. Header-only; included by the benchmark
// binaries, not part of the library API.

#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>
#include <gcs/stats.hh>
#include <gcs/variable_weighting.hh>

#include <atomic>
#include <chrono>
#include <optional>
#include <stop_token>
#include <string>
#include <thread>
#include <utility>

namespace gcs::bench
{
    // Map a dom-wdeg variant string to a weighting scheme, matching the langford
    // example's spelling (used by the `--branch dom-wdeg[:VARIANT]` flag).
    [[nodiscard]] inline auto scheme_from_string(const std::string & name) -> std::optional<WeightingScheme>
    {
        using enum WeightingScheme;
        if (name == "classic")
            return Classic;
        if (name == "ia")
            return InitialArity;
        if (name == "ca")
            return CurrentArity;
        if (name == "id")
            return InitialDomain;
        if (name == "cd")
            return CurrentDomain;
        if (name == "ca.cd" || name == "cacd")
            return CurrentArityCurrentDomain;
        if (name == "chs")
            return ConflictHistorySearch;
        return std::nullopt;
    }

    // Run solve_with, aborting the solve gracefully after `timeout_seconds`
    // (<= 0 means no limit) so that a capped run still returns the statistics it
    // had reached. A background timer sets the solver's abort flag at the
    // deadline; it is asked to stop as soon as the solve returns.
    [[nodiscard]] inline auto solve_with_timeout(double timeout_seconds, Problem & problem,
        SolveCallbacks callbacks, const std::optional<ProofOptions> & proof = std::nullopt) -> Stats
    {
        if (timeout_seconds <= 0.0)
            return solve_with(problem, std::move(callbacks), proof);

        std::atomic<bool> abort_flag{false};
        std::jthread timer([&abort_flag, timeout_seconds](std::stop_token stop) {
            const auto deadline = std::chrono::steady_clock::now() + std::chrono::duration<double>(timeout_seconds);
            while (! stop.stop_requested() && std::chrono::steady_clock::now() < deadline)
                std::this_thread::sleep_for(std::chrono::milliseconds(20));
            if (! stop.stop_requested())
                abort_flag.store(true);
        });

        auto stats = solve_with(problem, std::move(callbacks), proof, &abort_flag);
        timer.request_stop();
        return stats;
    }
}

#endif
