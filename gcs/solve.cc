#include <gcs/constraints/nogoods/nogoods.hh>
#include <gcs/exception.hh>
#include <gcs/innards/conflict_observer.hh>
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

#include <cstdlib>
#include <limits>
#include <string>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::make_shared;
using std::max;
using std::nullopt;
using std::numeric_limits;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::vector;
using std::chrono::duration_cast;
using std::chrono::microseconds;
using std::chrono::steady_clock;

namespace
{
    /**
     * How a (sub)tree exploration finished, so the caller knows how to unwind.
     * Complete: the subtree was fully explored; carry on with siblings/parent.
     * Stop: stop the whole search (abort flag, or a callback returned false) ---
     * the proof is abandoned, so we return immediately without balancing levels.
     * RestartCutoffHit is unused here and is produced once the restart loop lands;
     * unlike Stop it must unwind through the normal backtrack/forget logging so
     * the proof stays balanced for the restart that follows.
     */
    enum class SearchResult
    {
        Complete,
        Stop,
        RestartCutoffHit
    };

    /**
     * The restart budget threaded through the recursion: how many conflicts
     * (dead-end nodes) the current run has seen, and the cutoff at which it
     * should abandon the tree and restart. When restarts are disabled the cutoff
     * is "infinite", so the check never fires and search is a single pass.
     */
    struct RestartState
    {
        unsigned long long conflicts_since_restart;
        unsigned long long cutoff;
        bool enabled;
    };

    auto solve_with_state(unsigned long long depth, Stats & stats, Problem & problem, Propagators & propagators, State & state,
        const optional<Literal> & this_branch_guess, SolveCallbacks & callbacks, const BranchCallback & branch_callback, ProofLogger * const logger,
        bool & this_subtree_contains_solution, Integer & number_of_solutions, optional<Integer> & objective_value, RestartState & restart,
        NogoodStore * const learned_nogoods, const vector<IntegerVariableCondition> & reduced_prefix, atomic<bool> * optional_abort_flag)
        -> SearchResult
    {
        stats.max_depth = max(stats.max_depth, depth);
        ++stats.recursions;

        if (logger)
            logger->enter_proof_level(depth + 1);

        auto result = SearchResult::Complete;

        // Branch decisions this frame tried and whose subtree was then fully
        // refuted, before any restart cutoff hit. On a restart unwind each is a
        // learned nogood (the path to here plus that decision).
        vector<Literal> refuted_siblings;

        if (restart.conflicts_since_restart >= restart.cutoff) {
            // This run has spent its conflict budget: abandon the tree and unwind
            // to the root for a restart. Unlike Stop we fall through to the tail
            // backtrack/forget logging below, at this and every ancestor frame, so
            // the proof stays balanced and the restart can continue it.
            result = SearchResult::RestartCutoffHit;
        }
        else {
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
                    return SearchResult::Stop;

                auto branch_generator = branch_callback(state.current(), propagators);
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
                        return SearchResult::Stop;

                    // Continuing past a solution while restarting is sound: the
                    // proof's solx excludes each solution, so a fully-explored
                    // subtree (solutions and all) is refuted and the nld nogood
                    // learned for it stops a later pass re-entering and re-counting
                    // it. So enumeration accumulates each solution exactly once.
                }
                else {
                    if (callbacks.trace && ! callbacks.trace(state.current()))
                        return SearchResult::Stop;

                    if (optional_abort_flag && optional_abort_flag->load())
                        return SearchResult::Stop;

                    auto recurse = [&](const Literal & guess, const vector<IntegerVariableCondition> & child_prefix) -> SearchResult {
                        if (optional_abort_flag && optional_abort_flag->load())
                            return SearchResult::Stop;

                        auto timestamp = state.new_epoch();
                        state.guess(guess);
                        bool child_contains_solution = false;
                        auto child_result = solve_with_state(depth + 1, stats, problem, propagators, state, guess, callbacks, branch_callback, logger,
                            child_contains_solution, number_of_solutions, objective_value, restart, learned_nogoods, child_prefix,
                            optional_abort_flag);

                        if (child_contains_solution)
                            this_subtree_contains_solution = true;
                        else
                            ++stats.failures;

                        state.backtrack(timestamp);
                        return child_result;
                    };

                    // Reduced nld-nogoods thread down only the *positive* branch
                    // decisions. A binary branch's second sibling is the negation of
                    // its first (x=v then x!=v, or x<=v then x>v): descending into it
                    // is a refutation flip --- a negative decision --- so it is
                    // dropped, because the first sibling's own recorded nogood
                    // re-derives it on the next pass. Every other descended sibling
                    // (a first sibling, or any d-way value) is a free positive
                    // decision and extends the prefix.
                    optional<IntegerVariableCondition> first_sibling;
                    unsigned long long sibling_index = 0;
                    for (; branch_iter != branch_generator.end(); ++branch_iter) {
                        auto guess = *branch_iter;
                        // Only maintain the reduced prefix when we are actually
                        // learning nogoods: otherwise reduced_prefix stays empty and
                        // the copy is free, so ordinary search pays nothing.
                        auto child_prefix = reduced_prefix;
                        if (learned_nogoods) {
                            bool negative_flip = sibling_index == 1 && first_sibling && guess == ! *first_sibling;
                            if (! negative_flip)
                                child_prefix.push_back(guess);
                            if (sibling_index == 0)
                                first_sibling = guess;
                            ++sibling_index;
                        }

                        auto child_result = recurse(guess, child_prefix);
                        if (child_result == SearchResult::Stop)
                            return SearchResult::Stop;
                        if (child_result == SearchResult::RestartCutoffHit) {
                            result = SearchResult::RestartCutoffHit;
                            break;
                        }
                        // Complete: this sibling's subtree was refuted under the
                        // current path, so record it for restart-nogood learning.
                        refuted_siblings.push_back(guess);
                    }
                }
            }
            else {
                // A dead end: either the objective bound or a propagator wiped out
                // a domain. That is one conflict spent against the restart budget.
                ++restart.conflicts_since_restart;
            }
        }

        // Restart-nogood learning: each sibling refuted at this frame before the
        // cutoff yields a reduced nld-nogood --- the positive decisions on the path
        // to here (reduced_prefix) plus that refuted decision. The clause drops the
        // negative (refutation-flip) path decisions but is still RUP: this is logged
        // during the deep-first unwind, when the ancestor frames' backtrack lemmas
        // (which force exactly those dropped negatives) are still live below Top, so
        // RUP re-derives them. We derive it at Top so it survives the forget below
        // and the whole restart, and feed it to the store for the next pass.
        if (learned_nogoods && result == SearchResult::RestartCutoffHit && ! refuted_siblings.empty()) {
            for (const auto & sibling : refuted_siblings) {
                // The refuted sibling heads the nogood; if it is not a plain
                // condition (a proof-scaffolding literal) skip it.
                auto sibling_cond = std::get_if<IntegerVariableCondition>(&sibling);
                if (! sibling_cond)
                    continue;
                Nogood nogood = reduced_prefix;
                nogood.push_back(*sibling_cond);
                if (logger) {
                    vector<Literal> decisions;
                    decisions.reserve(reduced_prefix.size() + 1);
                    for (const auto & cond : reduced_prefix)
                        decisions.push_back(cond);
                    decisions.push_back(*sibling_cond);
                    logger->emit_learned_nogood(decisions);
                }
                learned_nogoods->add(move(nogood));
            }
        }

        if (logger) {
            logger->enter_proof_level(depth);
            if (result == SearchResult::RestartCutoffHit) {
                // We must NOT delete the root node's own guess-independent
                // propagation (proof level 1): the next pass starts from the same
                // root fixpoint, so propagate() re-emits nothing there, and that
                // reasoning has to survive for the next pass's backtracks to remain
                // RUP. So at the root (depth 0) we keep level 1; deeper
                // guess-dependent levels are re-derived next pass.
                if (depth > 0)
                    logger->forget_proof_level(depth + 1);
            }
            else {
                // A normal backtrack: the subtree under these guesses was refuted,
                // so we may assert the negation of the guess set (RUP from the
                // refutation that the forget below then discards).
                vector<Literal> guesses;
                for (const auto & g : state.guesses())
                    guesses.push_back(g);
                logger->backtrack(guesses);
                logger->forget_proof_level(depth + 1);
            }
        }

        return result;
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
    auto propagators = problem.create_propagators(state, optional_proof ? optional_proof->model() : nullptr);

    // With restarts on, search learns nogoods from refuted regions. Install an
    // (initially empty) Nogoods over a store the restart loop grows, subscribed
    // to every variable since a later-learned nogood may mention any. This is
    // engine-owned, not user-posted --- restart nogoods are internal (and, under
    // parallel search, per-thread). Must precede the model finalise below.
    shared_ptr<NogoodStore> nogood_store;
    if (callbacks.restarts) {
        nogood_store = make_shared<NogoodStore>();
        // Use refined per-literal watches for the learned-nogood store (issue #335,
        // stage C-2): the propagator wakes only when a learned clause loses a
        // non-entailed literal and visits only the clauses that fired, rather than
        // the coarse wake-on-every-variable-and-scan-the-whole-store path that was
        // the ~13.1M-wasted-propagation cost. Setting GCS_LEARNED_NOGOODS_SCAN picks
        // the legacy scan path, for the scan-vs-refined differential and perf check.
        bool refined_nogoods = (std::getenv("GCS_LEARNED_NOGOODS_SCAN") == nullptr);
        auto nogoods_constraint = Nogoods{nogood_store, problem.all_normal_variables(), refined_nogoods};
        nogoods_constraint.set_constraint_id(NamedConstraint{"learned_nogoods"});
        std::move(nogoods_constraint).install(propagators, state, optional_proof ? optional_proof->model() : nullptr);
    }

    if (optional_proof) {
        if (problem.optional_minimise_variable())
            optional_proof->model()->minimise(*problem.optional_minimise_variable());

        optional_proof->model()->preserve(problem.all_normal_variables());

        optional_proof->model()->finalise();
        optional_proof->model()->names_and_ids_tracker().switch_from_model_to_proof(optional_proof->logger());
        optional_proof->logger()->start_proof(*optional_proof->model());
        optional_proof->model()->names_and_ids_tracker().emit_delayed_proof_steps();

        if (auto & fn = optional_proof_options->proof_file_names.s_expr_file)
            write_scp(*fn, problem, optional_proof->model());
    }

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

        // Run the branching heuristic's per-search setup once, now that
        // propagators (and any presolver-added constraints) are final, so a
        // stateful heuristic sizes and attaches itself correctly; the resulting
        // per-node BranchCallback is reused throughout the search.
        auto branch_heuristic =
            callbacks.branch ? callbacks.branch : branch_with(variable_order::dom_then_deg(problem), value_order::smallest_first());
        auto branch_callback = branch_heuristic(problem, state, propagators);

        // A restart loop around the depth-first search: each pass explores until
        // it has spent its conflict cutoff, then unwinds to the root (proof
        // balanced) and the schedule grows the cutoff for the next pass. Weights
        // and the incumbent objective bound persist across passes, so a later pass
        // searches differently; the growing Luby cutoff eventually exceeds the
        // whole tree, so a final pass completes. Without a schedule the cutoff is
        // infinite and this is a single, exhaustive pass.
        auto restart_schedule = callbacks.restarts;
        RestartState restart{.conflicts_since_restart = 0,
            .cutoff = restart_schedule ? restart_schedule->current_cutoff() : numeric_limits<unsigned long long>::max(),
            .enabled = restart_schedule.has_value()};

        SearchResult search_result;
        do {
            restart.conflicts_since_restart = 0;
            search_result = solve_with_state(0, stats, problem, propagators, state, nullopt, callbacks, branch_callback,
                optional_proof ? optional_proof->logger() : nullptr, child_contains_solution, number_of_solutions, objective_value, restart,
                nogood_store.get(), vector<IntegerVariableCondition>{}, optional_abort_flag);

            if (search_result == SearchResult::RestartCutoffHit) {
                ++stats.restarts;
                for (auto & observer : propagators.conflict_observers())
                    observer->on_restart();
                restart_schedule->advance();
                restart.cutoff = restart_schedule->current_cutoff();
            }
        } while (search_result == SearchResult::RestartCutoffHit);

        if (search_result == SearchResult::Complete) {
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
    if (nogood_store)
        stats.learned_nogoods = nogood_store->size();

    return stats;
}

auto gcs::solve(Problem & problem, SolutionCallback callback, const optional<ProofOptions> & proof_options) -> Stats
{
    return solve_with(problem, SolveCallbacks{.solution = callback}, proof_options);
}
