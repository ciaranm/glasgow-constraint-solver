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
                auto lower = lower_bound(state.integer_variable(*branch_var)), upper = upper_bound(state.integer_variable(*branch_var));
                for ( ; lower <= upper ; ++lower) {
                    if (in_domain(state.integer_variable(*branch_var), lower)) {
                        auto new_state = state.clone();
                        switch (new_state.infer(*branch_var == lower)) {
                            case Inference::NoChange:
                            case Inference::Change:
                                if (! solve_with_state(depth + 1, stats, problem, new_state, callback))
                                    return false;
                                break;
                            case Inference::Contradiction:
                                throw UnexpectedException{ "couldn't infer a branch?" };
                        }
                    }
                }
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

