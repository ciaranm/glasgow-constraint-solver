/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/solve.hh"
#include "gcs/exception.hh"

using namespace gcs;

using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;
using std::max;
using std::nullopt;

namespace
{
    auto solve_with_state(unsigned long long depth, Stats & stats, const Problem & problem, State & state, SolutionCallback & callback) -> bool
    {
        stats.max_depth = max(stats.max_depth, depth);
        ++stats.recursions;

        if (problem.propagate(state)) {
            auto branch_var = problem.find_branching_variable(state);
            if (branch_var == nullopt) {
                ++stats.solutions;
                if (! callback(state))
                    return false;
            }
            else {
                bool keep_going = true;
                state.for_each_value(*branch_var, [&] (Integer val) {
                        if (keep_going) {
                            auto new_state = state.clone();
                            new_state.guess(*branch_var == val);
                            if (! solve_with_state(depth + 1, stats, problem, new_state, callback))
                                keep_going = false;
                        }
                    });

                if (! keep_going)
                    return false;
            }
        }

        return true;
    }
}

auto gcs::solve(const Problem & problem, SolutionCallback callback) -> Stats
{
    Stats stats;
    auto start_time = steady_clock::now();

    State state = problem.create_initial_state();
    solve_with_state(0, stats, problem, state, callback);

    stats.solve_time = duration_cast<microseconds>(steady_clock::now() - start_time);
    return stats;
}

