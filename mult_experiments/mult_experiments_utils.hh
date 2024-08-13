#ifndef MULT_EXPERIMENTS_UTILS_HH
#define MULT_EXPERIMENTS_UTILS_HH

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <csignal>
#include <gcs/gcs.hh>
#include <mutex>
#include <optional>
#include <thread>

namespace gcs::test_innards
{
    enum MultTestType
    {
        NO_PROOFS,
        BC_PROOFS,
        DC_PROOFS
    };

    static std::atomic<bool> abort_flag{false}, was_terminated{false};

    auto sig_int_or_term_handler(int) -> void
    {
        abort_flag.store(true);
        was_terminated.store(true);
    }

    auto solve_with_timeout(Problem & problem, SolveCallbacks callbacks,
        const std::optional<ProofOptions> & optional_proof_options, const long timeout_seconds) -> Stats
    {
        signal(SIGINT, &sig_int_or_term_handler);
        signal(SIGTERM, &sig_int_or_term_handler);

        std::thread timeout_thread;
        std::mutex timeout_mutex;
        std::condition_variable timeout_cv;
        bool actually_timed_out = false;

        std::chrono::milliseconds limit{timeout_seconds * 1000};

        timeout_thread = std::thread([limit = limit, &timeout_mutex, &timeout_cv, &actually_timed_out] {
            auto abort_time = std::chrono::system_clock::now() + limit;
            {
                /* Sleep until either we've reached the time limit,
                 * or we've finished all the work. */
                std::unique_lock<std::mutex> guard(timeout_mutex);
                while (! abort_flag.load()) {
                    if (std::cv_status::timeout == timeout_cv.wait_until(guard, abort_time)) {
                        /* We've woken up, and it's due to a timeout. */
                        actually_timed_out = true;
                        break;
                    }
                }
            }
            abort_flag.store(true);
        });

        auto stats = solve_with(problem, std::move(callbacks), optional_proof_options, &abort_flag);
        if (timeout_thread.joinable()) {
            {
                std::unique_lock<std::mutex> guard(timeout_mutex);
                abort_flag.store(true);
                timeout_cv.notify_all();
            }
            timeout_thread.join();
        }

        return stats;
    }
}
#endif