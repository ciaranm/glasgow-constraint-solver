/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH 1

#include <chrono>

namespace gcs
{
    struct Stats
    {
        unsigned long long recursions;
        unsigned long long solutions;
        unsigned long long max_depth;

        std::chrono::microseconds solve_time;
    };
}

#endif
