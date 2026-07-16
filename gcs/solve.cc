#include <gcs/exception.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/scp_writer.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/proof.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <util/enumerate.hh>

#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::max;
using std::nullopt;
using std::optional;
using std::pair;
using std::vector;
using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;

namespace
{
    auto solve_with_state(unsigned long long depth, Stats & stats, Problem & problem, Propagators & propagators, State & state,
        const optional<Literal> & this_branch_guess, SolveCallbacks & callbacks, ProofLogger * const logger, bool & this_subtree_contains_solution,
        Integer & number_of_solutions, optional<Integer> & objective_value, atomic<bool> * optional_abort_flag) -> bool
    {
        stats.max_depth = max(stats.max_depth, depth);
        ++stats.recursions;

        if (logger)
            logger->enter_proof_level(depth + 1);

        bool objective_failure = false;
        Literals guesses;
        if (this_branch_guess)
            guesses.push_back(*this_branch_guess);
        if (problem.optional_minimise_variable() && objective_value) {
            auto objective_bound = *problem.optional_minimise_variable() < *objective_value;
            switch (state.infer(objective_bound)) {
            case Inference::Contradiction: objective_failure = true; break;
            case Inference::NoChange: break;
            // The branch-and-bound bound tightened the objective variable, so seed the queue with
            // its propagators too. Without this only this_branch_guess seeds the queue, and a
            // propagator that would react to the new objective bound is not re-run here (issue #418).
            case Inference::BoundsChanged:
            case Inference::InteriorValuesChanged:
            case Inference::Instantiated: guesses.push_back(objective_bound); break;
            }
        }

        if ((! objective_failure) && propagators.propagate(guesses, state, logger, optional_abort_flag)) {
            if (optional_abort_flag && optional_abort_flag->load())
                return false;

            auto branch_generator = callbacks.branch(state.current(), propagators);
            auto branch_iter = branch_generator.begin();

            if (branch_iter == branch_generator.end()) {
                if (logger) {
                    vector<pair<IntegerVariableID, Integer>> vars_and_values;
                    for (const auto & v : problem.all_normal_variables())
                        vars_and_values.emplace_back(v, state(v));
                    logger->solution(vars_and_values,
                        problem.optional_minimise_variable().transform([&](const IntegerVariableID & var) { return pair{var, state(var)}; }));
                }

                if (problem.optional_minimise_variable())
                    objective_value = state(*problem.optional_minimise_variable());

                ++stats.solutions;
                ++number_of_solutions;
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
                    state.guess(guess);
                    bool child_contains_solution = false;
                    if (! solve_with_state(depth + 1, stats, problem, propagators, state, guess, callbacks, logger, child_contains_solution,
                            number_of_solutions, objective_value, optional_abort_flag))
                        result = false;

                    if (child_contains_solution)
                        this_subtree_contains_solution = true;
                    else
                        ++stats.failures;

                    state.backtrack(timestamp);
                    return result;
                };

                for (; branch_iter != branch_generator.end(); ++branch_iter) {
                    auto guess = *branch_iter;
                    if (! recurse(guess))
                        return false;
                }
            }
        }

        if (logger) {
            logger->enter_proof_level(depth);
            vector<Literal> guesses;
            for (const auto & g : state.guesses())
                guesses.push_back(g);
            logger->backtrack(guesses);
            logger->forget_proof_level(depth + 1);
        }

        return true;
    }
}

auto gcs::solve_with(
    Problem & problem, SolveCallbacks callbacks, const optional<ProofOptions> & optional_proof_options, atomic<bool> * optional_abort_flag) -> Stats
{
    Stats stats;
    auto start_time = steady_clock::now();

    optional<Proof> optional_proof;
    if (optional_proof_options) {
        optional_proof.emplace(*optional_proof_options);
    }

    auto state = problem.create_state_for_new_search(optional_proof ? optional_proof->model() : nullptr);

    if (optional_proof) {
        if (problem.optional_minimise_variable())
            optional_proof->model()->minimise(*problem.optional_minimise_variable());

        optional_proof->model()->preserve(problem.all_normal_variables());

        // Every variable the objective and preserve list mention now exists,
        // so the OPB front matter can go out; the constraint definitions that
        // follow stream straight to the file.
        optional_proof->model()->write_preamble();
    }

    auto propagators = problem.create_propagators(state, optional_proof ? optional_proof->model() : nullptr);

    if (optional_proof) {
        optional_proof->model()->finalise();
        optional_proof->model()->names_and_ids_tracker().switch_from_model_to_proof(optional_proof->logger());
        optional_proof->logger()->start_proof(*optional_proof->model());
        optional_proof->model()->names_and_ids_tracker().emit_delayed_proof_steps();

        if (auto & fn = optional_proof_options->proof_file_names.s_expr_file)
            write_scp(*fn, problem, optional_proof->model());
    }

    // solve_with_state invokes callbacks.branch unconditionally: an unset
    // branch callback is filled in with the default heuristic here, once,
    // rather than testing and copying the std::function (and every closure
    // the composed heuristics capture) at every node of the recursion.
    if (! callbacks.branch)
        callbacks.branch = branch_with(variable_order::dom_then_deg(problem), value_order::smallest_first());

    if (callbacks.after_proof_started)
        callbacks.after_proof_started(state.current());

    auto initialisation_success = propagators.initialise(state, optional_proof ? optional_proof->logger() : nullptr);

    auto presolve_success = initialisation_success;
    if (initialisation_success) {
        for (auto & presolver : problem.each_presolver()) {
            if (! presolver.run(problem, propagators, state, optional_proof ? optional_proof->logger() : nullptr)) {
                presolve_success = false;
                break;
            }
        }
    }

    Integer objective_lower_bound_for_proof = 0_i;
    if (optional_proof && problem.optional_minimise_variable())
        objective_lower_bound_for_proof = state.lower_bound(*problem.optional_minimise_variable());

    if (initialisation_success && presolve_success) {
        bool child_contains_solution = false;
        Integer number_of_solutions = 0_i;
        optional<Integer> objective_value = nullopt;
        if (solve_with_state(0, stats, problem, propagators, state, nullopt, callbacks, optional_proof ? optional_proof->logger() : nullptr,
                child_contains_solution, number_of_solutions, objective_value, optional_abort_flag)) {
            if (optional_proof) {
                if (problem.optional_minimise_variable()) {
                    if (objective_value)
                        optional_proof->logger()->conclude_optimality(*problem.optional_minimise_variable(), *objective_value);
                    else
                        optional_proof->logger()->conclude_unsatisfiable(true);
                }
                else if (child_contains_solution) {
                    optional_proof->logger()->conclude_complete_enumeration(number_of_solutions);
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
                        optional_proof->logger()->conclude_bounds(
                            *problem.optional_minimise_variable(), objective_lower_bound_for_proof, *objective_value);
                    else
                        optional_proof->logger()->conclude_none();
                }
                else if (child_contains_solution)
                    optional_proof->logger()->conclude_satisfiable();
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

    if (optional_proof)
        optional_proof->model()->names_and_ids_tracker().finalise();

    stats.solve_time = duration_cast<microseconds>(steady_clock::now() - start_time);
    propagators.fill_in_constraint_stats(stats);

    return stats;
}

auto gcs::solve(Problem & problem, SolutionCallback callback, const optional<ProofOptions> & proof_options) -> Stats
{
    return solve_with(problem, SolveCallbacks{.solution = callback}, proof_options);
}
