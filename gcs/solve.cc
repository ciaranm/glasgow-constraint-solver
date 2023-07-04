#include <gcs/exception.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>
#include <fstream>
#include <iostream>


using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::max;
using std::nullopt;
using std::optional;
using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;

namespace
{
    auto solve_with_state(unsigned long long depth, Stats & stats, Problem & problem,
        Propagators & propagators, State & state,
        SolveCallbacks & callbacks, optional<Proof> & optional_proof,
        bool & this_subtree_contains_solution,
        atomic<bool> * optional_abort_flag) -> bool
    {
        stats.max_depth = max(stats.max_depth, depth);
        ++stats.recursions;

        if (optional_proof)
            optional_proof->enter_proof_level(depth + 1);

        if (propagators.propagate(state, optional_abort_flag)) {
            if (optional_abort_flag && optional_abort_flag->load())
                return false;

            auto branch_var = callbacks.branch ? callbacks.branch(state.current(), propagators) : branch_on_dom_then_deg(problem)(state.current(), propagators);
            if (branch_var == nullopt) {
                if (optional_proof)
                    optional_proof->solution(state);

                ++stats.solutions;
                this_subtree_contains_solution = true;
                if (callbacks.solution && ! callbacks.solution(state.current()))
                    return false;

                state.update_objective_to_current_solution();
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
                    if (! solve_with_state(depth + 1, stats, problem, propagators, state,
                            callbacks, optional_proof, child_contains_solution, optional_abort_flag))
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

        if (optional_proof) {
            optional_proof->enter_proof_level(depth);
            optional_proof->backtrack(state);
            optional_proof->forget_proof_level(depth + 1);
        }

        return true;
    }
}

auto gcs::solve_with(Problem & problem, SolveCallbacks callbacks,
    const optional<ProofOptions> & optional_proof_options,
    atomic<bool> * optional_abort_flag) -> Stats
{
    Stats stats;
    auto start_time = steady_clock::now();

    optional<Proof> optional_proof;
    if (optional_proof_options)
        optional_proof = Proof{*optional_proof_options};

    auto state = problem.create_state_for_new_search(optional_proof);
    auto propagators = problem.create_propagators(state, optional_proof);

    if (optional_proof)
        optional_proof->start_proof(state);

    if (callbacks.after_proof_started)
        callbacks.after_proof_started(state.current());

    propagators.initialise(state);

    auto presolve_success = problem.for_each_presolver([&](Presolver & presolver) -> bool {
        auto result = presolver.run(problem, propagators, state);
        propagators.requeue_all_propagators();
        return result;
    });

    if (presolve_success) {
        bool child_contains_solution = false;
        if (solve_with_state(0, stats, problem, propagators, state, callbacks, optional_proof,
                child_contains_solution, optional_abort_flag))
            if (optional_proof)
                optional_proof->assert_contradiction();
    }
    else if (optional_proof)
        optional_proof->assert_contradiction();

    stats.solve_time = duration_cast<microseconds>(steady_clock::now() - start_time);
    propagators.fill_in_constraint_stats(stats);

    if (optional_proof) {

        std::string str = optional_proof_options.value().opb_file;
        // std::size_t pos = str.find('.');
        std::string name_file = str.substr(0, str.length() - 4);
        name_file += "_computation_time_2_threads_work";

        std::ofstream file;
        file.open(name_file, std::ofstream::out | std::ofstream::app);

        if (file) {
            file << std::to_string(stats.solve_time.count() / 1'000'000.0) << std::endl;
            file.close();
        }
        else
            std::cout << "Impossible to open the file" << std::endl;
    }

    return stats;
}

auto gcs::solve(Problem & problem, SolutionCallback callback,
    const optional<ProofOptions> & proof_options) -> Stats
{
    return solve_with(problem, SolveCallbacks{.solution = callback}, proof_options);
}
