/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/state.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::max;
using std::nullopt;
using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;

namespace
{
    auto solve_with_state(unsigned long long depth, Stats & stats, Problem & problem, State & state,
        SolveCallbacks & callbacks, bool & this_subtree_contains_solution,
        atomic<bool> * optional_abort_flag) -> bool
    {
        stats.max_depth = max(stats.max_depth, depth);
        ++stats.recursions;

        if (problem.optional_proof())
            problem.optional_proof()->enter_proof_level(depth + 1);

        if (problem.propagate(state, optional_abort_flag)) {
            if (optional_abort_flag && optional_abort_flag->load())
                return false;

            auto branch_var = callbacks.branch ? callbacks.branch(state.current()) : branch_on_dom_then_deg(problem)(state.current());
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
                if (callbacks.trace && ! callbacks.trace(state.current()))
                    return false;

                if (optional_abort_flag && optional_abort_flag->load())
                    return false;

                auto recurse = [&](const Literal & guess) -> bool {
                    if (optional_abort_flag && optional_abort_flag->load())
                        return false;

                    auto result = true;
                    auto timestamp = state.new_epoch();
                    state.guess(guess);
                    bool child_contains_solution = false;
                    if (! solve_with_state(depth + 1, stats, problem, state, callbacks, child_contains_solution, optional_abort_flag))
                        result = false;

                    if (child_contains_solution)
                        this_subtree_contains_solution = true;
                    else
                        ++stats.failures;

                    state.backtrack(timestamp);
                    return result;
                };

                if (callbacks.guess) {
                    auto guesses = callbacks.guess(state.current(), *branch_var);
                    for (auto & guess : guesses)
                        if (! recurse(guess))
                            return false;
                }
                else {
                    if (! state.for_each_value_while(*branch_var, [&](Integer val) {
                            return recurse(*branch_var == val);
                        }))
                        return false;
                }
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

auto gcs::solve_with(Problem & problem, SolveCallbacks callbacks, atomic<bool> * optional_abort_flag) -> Stats
{
    Stats stats;
    auto start_time = steady_clock::now();

    State state = problem.create_state();
    if (problem.optional_proof())
        problem.optional_proof()->start_proof(state);

    if (callbacks.after_proof_started)
        callbacks.after_proof_started(state.current());

    bool child_contains_solution = false;
    if (solve_with_state(0, stats, problem, state, callbacks, child_contains_solution, optional_abort_flag))
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
