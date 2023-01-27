#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH

#include <chrono>
#include <iosfwd>
#include <string>
#include <tuple>
#include <vector>

namespace gcs
{
    /**
     * \brief Statistics from solving.
     *
     * \sa gcs::solve()
     * \sa gcs::solve_with()
     * \ingroup Core
     */
    struct Stats
    {
        unsigned long long recursions = 0;
        unsigned long long failures = 0;
        unsigned long long propagations = 0;
        unsigned long long effectful_propagations = 0;
        unsigned long long contradicting_propagations = 0;
        unsigned long long solutions = 0;
        unsigned long long max_depth = 0;

        unsigned long long n_propagators = 0;

        std::chrono::microseconds solve_time;
    };

    /**
     * \brief Stats can be written to an ostream, for convenience.
     *
     * \sa Stats
     * \ingroup Core
     */
    auto operator<<(std::ostream &, const Stats &) -> std::ostream &;
}

#endif
