#include <gcs/exception.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/proof.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

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
        SolveCallbacks & callbacks,
        ProofLogger * const logger,
        bool & this_subtree_contains_solution,
        optional<Integer> & objective_value,
        atomic<bool> * optional_abort_flag) -> bool
    {
        stats.max_depth = max(stats.max_depth, depth);
        ++stats.recursions;

        if (logger)
            logger->enter_proof_level(depth + 1);

        bool objective_failure = false;
        if (problem.optional_minimise_variable() && objective_value) {
            if (state.infer(logger, *problem.optional_minimise_variable() < *objective_value, NoJustificationNeeded{},
                    Reason{}) == Inference::Contradiction)
                objective_failure = true;
        }

        if ((! objective_failure) && propagators.propagate(state, logger, optional_abort_flag)) {
            if (optional_abort_flag && optional_abort_flag->load())
                return false;

            auto branch_var = callbacks.branch ? callbacks.branch(state.current(), propagators) : branch_on_dom_then_deg(problem)(state.current(), propagators);
            if (branch_var == nullopt) {
                if (logger)
                    logger->solution(state, problem.all_normal_variables(), problem.optional_minimise_variable());

                if (problem.optional_minimise_variable())
                    objective_value = state(*problem.optional_minimise_variable());

                ++stats.solutions;
                this_subtree_contains_solution = true;
                if (callbacks.solution && ! callbacks.solution(state.current()))
                    return false;
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
                    state.guess(logger, guess);
                    bool child_contains_solution = false;
                    if (! solve_with_state(depth + 1, stats, problem, propagators, state,
                            callbacks, logger, child_contains_solution, objective_value, optional_abort_flag))
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

        if (logger) {
            logger->enter_proof_level(depth);
            logger->backtrack(state);
            logger->forget_proof_level(depth + 1);
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
        optional_proof.emplace(*optional_proof_options);

    auto state = problem.create_state_for_new_search(optional_proof ? optional_proof->model() : nullptr);
    auto propagators = problem.create_propagators(state, optional_proof ? optional_proof->model() : nullptr);

    if (optional_proof) {
        if (problem.optional_minimise_variable())
            optional_proof->model()->minimise(*problem.optional_minimise_variable());
        optional_proof->model()->finalise();
        optional_proof->model()->variable_constraints_tracker().switch_from_model_to_proof(optional_proof->logger());
        optional_proof->logger()->start_proof(*optional_proof->model());
    }

    if (callbacks.after_proof_started)
        callbacks.after_proof_started(state.current());

    auto initialisation_success = propagators.initialise(state, optional_proof ? optional_proof->logger() : nullptr);

    auto presolve_success = (! initialisation_success) ? false : problem.for_each_presolver([&](Presolver & presolver) -> bool {
        auto result = presolver.run(problem, propagators, state, optional_proof ? optional_proof->logger() : nullptr);
        propagators.requeue_all_propagators();
        return result;
    });

    Integer objective_lower_bound_for_proof = 0_i;
    if (optional_proof && problem.optional_minimise_variable())
        objective_lower_bound_for_proof = state.lower_bound(*problem.optional_minimise_variable());

    if (initialisation_success && presolve_success) {
        bool child_contains_solution = false;
        optional<Integer> objective_value = nullopt;
        if (solve_with_state(0, stats, problem, propagators, state, callbacks, optional_proof ? optional_proof->logger() : nullptr,
                child_contains_solution, objective_value, optional_abort_flag)) {
            if (optional_proof) {
                if (problem.optional_minimise_variable()) {
                    if (objective_value)
                        optional_proof->logger()->conclude_optimality(*problem.optional_minimise_variable(), *objective_value);
                    else
                        optional_proof->logger()->conclude_unsatisfiable(true);
                }
                else if (child_contains_solution) {
                    optional_proof->logger()->conclude_satisfiable();
                }
                else
                    optional_proof->logger()->conclude_unsatisfiable(false);
            }

            if (callbacks.completed)
                callbacks.completed();
        }
        else {
            // finished without a full conclusion
            if (optional_proof) {
                if (problem.optional_minimise_variable()) {
                    if (objective_value)
                        optional_proof->logger()->conclude_bounds(*problem.optional_minimise_variable(),
                            objective_lower_bound_for_proof, *objective_value);
                    else
                        optional_proof->logger()->conclude_none();
                }
                else
                    optional_proof->logger()->conclude_none();
            }
        }
    }
    else {
        if (optional_proof)
            optional_proof->logger()->conclude_unsatisfiable(problem.optional_minimise_variable().has_value());
        if (callbacks.completed)
            callbacks.completed();
    }

    stats.solve_time = duration_cast<microseconds>(steady_clock::now() - start_time);
    propagators.fill_in_constraint_stats(stats);

    return stats;
}

auto gcs::solve(Problem & problem, SolutionCallback callback,
    const optional<ProofOptions> & proof_options) -> Stats
{
    return solve_with(problem, SolveCallbacks{.solution = callback}, proof_options);
}
