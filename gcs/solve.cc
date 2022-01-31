/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/detail/proof.hh>
#include <gcs/detail/state.hh>
#include <gcs/exception.hh>
#include <gcs/solve.hh>

using namespace gcs;

using std::max;
using std::nullopt;
using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;

namespace
{
    auto solve_with_state(unsigned long long depth, Stats & stats, Problem & problem, State & state,
        SolveCallbacks & callbacks, bool & this_subtree_contains_solution) -> bool
    {
        stats.max_depth = max(stats.max_depth, depth);
        ++stats.recursions;

        if (problem.optional_proof())
            problem.optional_proof()->enter_proof_level(depth + 1);

        if (problem.propagate(state)) {
            auto branch_var = callbacks.branch ? callbacks.branch(state.current()) : problem.find_branching_variable(state);
            if (branch_var == nullopt) {
                if (problem.optional_proof())
                    problem.optional_proof()->solution(state);

                ++stats.solutions;
                this_subtree_contains_solution = true;
                if (callbacks.solution && ! callbacks.solution(state.current()))
                    return false;

                problem.update_objective(state);
            }
            else {
                bool keep_going = true;

                if (callbacks.trace && ! callbacks.trace(state.current()))
                    keep_going = false;

                if (callbacks.guess) {
                    auto guesses = callbacks.guess(state.current(), *branch_var);
                    for (auto & guess : guesses) {
                        if (keep_going) {
                            auto timestamp = state.new_epoch();
                            state.guess(guess);
                            bool child_contains_solution = false;
                            if (! solve_with_state(depth + 1, stats, problem, state, callbacks, child_contains_solution))
                                keep_going = false;

                            if (child_contains_solution)
                                this_subtree_contains_solution = true;
                            else
                                ++stats.failures;

                            state.backtrack(timestamp);
                        }
                    }
                }
                else {
                    state.for_each_value(*branch_var, [&](Integer val) {
                        if (keep_going) {
                            auto timestamp = state.new_epoch();
                            state.guess(*branch_var == val);
                            bool child_contains_solution = false;
                            if (! solve_with_state(depth + 1, stats, problem, state, callbacks, child_contains_solution))
                                keep_going = false;

                            if (child_contains_solution)
                                this_subtree_contains_solution = true;
                            else
                                ++stats.failures;

                            state.backtrack(timestamp);
                        }
                    });
                }

                if (! keep_going)
                    return false;
            }
        }

        if (problem.optional_proof()) {
            problem.optional_proof()->enter_proof_level(depth);
            problem.optional_proof()->backtrack(state);
            problem.optional_proof()->forget_proof_level(depth + 1);
        }

        return true;
    }
}

auto gcs::solve_with(Problem & problem, SolveCallbacks callbacks) -> Stats
{
    Stats stats;
    auto start_time = steady_clock::now();

    State state = problem.create_state();
    if (problem.optional_proof())
        problem.optional_proof()->start_proof(state);

    if (callbacks.after_proof_started)
        callbacks.after_proof_started(state.current());

    bool child_contains_solution = false;
    if (solve_with_state(0, stats, problem, state, callbacks, child_contains_solution))
        if (problem.optional_proof())
            problem.optional_proof()->assert_contradiction();

    stats.solve_time = duration_cast<microseconds>(steady_clock::now() - start_time);
    problem.fill_in_constraint_stats(stats);

    return stats;
}

auto gcs::solve(Problem & problem, SolutionCallback callback) -> Stats
{
    return solve_with(problem, SolveCallbacks{.solution = callback});
}
