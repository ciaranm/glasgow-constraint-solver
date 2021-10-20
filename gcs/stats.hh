/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH 1

#include <chrono>
#include <iosfwd>
#include <string>
#include <tuple>
#include <vector>

namespace gcs
{
    struct Stats
    {
        unsigned long long recursions = 0;
        unsigned long long failures = 0;
        unsigned long long solutions = 0;
        unsigned long long max_depth = 0;

        unsigned long long n_cnfs = 0;
        unsigned long long n_propagators = 0;

        std::chrono::microseconds solve_time;
    };

    auto operator<< (std::ostream &, const Stats &) -> std::ostream &;
}

#endif
