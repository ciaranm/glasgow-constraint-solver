/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SOLVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SOLVE_HH 1

#include <gcs/problem.hh>
#include <gcs/state.hh>

#include <functional>

namespace gcs
{
    using SolutionCallback = std::function<auto (const State &) -> bool>;

    auto solve(const Problem &, SolutionCallback callback) -> void;
}

#endif
