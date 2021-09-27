/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SOLVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SOLVE_HH 1

#include <gcs/problem.hh>
#include <gcs/state.hh>
#include <gcs/stats.hh>

#include <functional>

namespace gcs
{
    using SolutionCallback = std::function<auto (const State &) -> bool>;
    using TraceCallback = std::function<auto (const State &) -> bool>;
    using BranchCallback = std::function<auto (const State &) -> std::optional<IntegerVariableID> >;

    struct SolveCallbacks
    {
        SolutionCallback solution = SolutionCallback{ };
        TraceCallback trace = TraceCallback{ };
        BranchCallback branch = BranchCallback{ };
    };

    auto solve(Problem &, SolutionCallback callback) -> Stats;

    auto solve_with(Problem &, SolveCallbacks ballbacks) -> Stats;
}

#endif
