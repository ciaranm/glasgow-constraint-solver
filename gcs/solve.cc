/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/solve.hh"
#include "gcs/exception.hh"

using namespace gcs;

using std::nullopt;

namespace
{
    auto solve_with_state(int depth, const Problem & problem, State & state, SolutionCallback & callback) -> bool
    {
        if (problem.propagate(state)) {
            auto branch_var = problem.find_branching_variable(state);
            if (branch_var == nullopt) {
                if (! callback(state))
                    return false;
            }
            else {
                auto lower = lower_bound(state.integer_variable(*branch_var)), upper = upper_bound(state.integer_variable(*branch_var));
                for ( ; lower <= upper ; ++lower) {
                    if (in_domain(state.integer_variable(*branch_var), lower)) {
                        auto new_state = state.clone();
                        if (new_state.infer(*branch_var == lower)) {
                            if (! solve_with_state(depth + 1, problem, new_state, callback))
                                return false;
                        }
                        else
                            throw UnexpectedException{ "couldn't infer a branch?" };
                    }
                }
            }
        }

        return true;
    }
}

auto gcs::solve(const Problem & problem, SolutionCallback callback) -> void
{
    State state = problem.create_initial_state();
    solve_with_state(0, problem, state, callback);
}

