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
#include <ranges>
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
using std::ranges::iterator_t;

namespace
{
    /**
     * How exploring a node finished, so the search knows how to unwind.
     * Complete: the subtree was fully explored; carry on with siblings/parent.
     * Stop: stop the whole search (abort flag, or a callback returned false) ---
     * the proof is abandoned, so we unwind immediately without balancing levels.
     * RestartCutoffHit: the restart cutoff was reached, so abandon this pass; unlike
     * Stop it must unwind through the normal backtrack/forget logging so
     * the proof stays balanced for the restart that follows.
     */
    enum class SearchResult
    {
        Complete,
        Stop,
        RestartCutoffHit
    };

    /**
     * The restart budget kept across the search: how many conflicts
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

    using Branches = std::generator<IntegerVariableCondition>;

    /**
     * A brancher's coroutine, and the branch it is up to. Both hold only a
     * handle to the coroutine's frame, so moving them, as the search path does
     * when it grows, leaves the iterator valid.
     */
    struct Branching
    {
        Branches generator;
        iterator_t<Branches> next;

        explicit Branching(Branches && g) : generator(std::move(g)), next(generator.begin())
        {
        }

        [[nodiscard]] auto exhausted() const -> bool
        {
            return next == generator.end();
        }
    };

    /**
     * A node on the current search path: everything the search keeps about it
     * while it explores the subtrees under it.
     */
    struct SearchNode
    {
        // The state to backtrack to when leaving this node: the one its
        // parent was in before guessing it. The root has none.
        optional<Timestamp> before_guess;

        // The positive branch decisions on the path to here, for restart
        // nogoods. See DepthFirstSearch::branch().
        vector<IntegerVariableCondition> reduced_prefix;

        // Whether a solution has been found anywhere under here.
        bool contains_solution;

        // Set once there is nothing more to explore under here.
        optional<SearchResult> outcome = nullopt;

        // Absent if the node was finished with before it got as far as
        // branching.
        optional<Branching> branching = nullopt;

        // For building the children's reduced prefixes.
        optional<IntegerVariableCondition> first_sibling = nullopt;
        unsigned long long sibling_index = 0;

        // Branch decisions this node tried and whose subtree was then fully
        // refuted, before any restart cutoff hit. On a restart unwind each is a
        // learned nogood (the path to here plus that decision). Only kept
        // when learning nogoods, since nothing else reads it.
        vector<Literal> refuted_siblings = {};

        SearchNode(const optional<Timestamp> & before_guess, vector<IntegerVariableCondition> && reduced_prefix, bool contains_solution) :
            before_guess(before_guess), reduced_prefix(std::move(reduced_prefix)), contains_solution(contains_solution)
        {
        }
    };

    /**
     * Depth-first search, one restart pass at a time.
     *
     * The path from the root to the node being explored is kept as an explicit
     * stack of SearchNode, rather than on the call stack, so how deep the search
     * can go is limited only by memory. Search used to recurse once per
     * decision, and on a default 8 MB stack that crashed past about 9,000
     * decisions (#1085).
     *
     * Everything here belongs to one call of solve_with(), so independent
     * searches share nothing.
     */
    class DepthFirstSearch
    {
    private:
        Problem & _problem;
        Propagators & _propagators;
        State & _state;
        Stats & _stats;
        SolveCallbacks & _callbacks;
        const BranchCallback & _branch_callback;
        ProofLogger * const _logger;
        NogoodStore * const _learned_nogoods;
        RestartState & _restart;
        atomic<bool> * const _optional_abort_flag;

        // The branchers in search_heuristics.cc are coroutines, so calling
        // _branch_callback only builds the frame: the CurrentState reference is
        // stored, and nothing reads it until begin() resumes the coroutine.
        // State::current() returns by value, so a temporary would be dead by
        // then. Every CurrentState here would refer to the same State, so the
        // branchers all share this one, which outlives them.
        CurrentState _current_state;

        vector<SearchNode> _path;

        [[nodiscard]] auto aborted() const -> bool
        {
            return _optional_abort_flag && _optional_abort_flag->load();
        }

        auto enter_node(const optional<Literal> & guess, const optional<Timestamp> & before_guess, vector<IntegerVariableCondition> && reduced_prefix)
            -> void;
        auto record_solution(SearchNode & node) -> bool;
        auto branch(SearchNode & node) -> void;
        auto finish_node(SearchNode & node) -> SearchResult;
        auto leave_node() -> void;

    public:
        // What the search has found so far, over every pass.
        bool found_solution = false;
        Integer number_of_solutions = 0_i;
        optional<Integer> objective_value = nullopt;

        DepthFirstSearch(Problem & problem, Propagators & propagators, State & state, Stats & stats, SolveCallbacks & callbacks,
            const BranchCallback & branch_callback, ProofLogger * const logger, NogoodStore * const learned_nogoods, RestartState & restart,
            atomic<bool> * const optional_abort_flag) :
            _problem(problem), _propagators(propagators), _state(state), _stats(stats), _callbacks(callbacks), _branch_callback(branch_callback),
            _logger(logger), _learned_nogoods(learned_nogoods), _restart(restart), _optional_abort_flag(optional_abort_flag),
            _current_state(state.current())
        {
        }

        /**
         * Explore the tree from the root until it is exhausted, the restart
         * cutoff hits, or search is to stop.
         */
        auto run_pass() -> SearchResult;
    };

    auto DepthFirstSearch::run_pass() -> SearchResult
    {
        enter_node(nullopt, nullopt, {});

        while (true) {
            auto & node = _path.back();

            if (! node.outcome) {
                if (! node.branching->exhausted()) {
                    branch(node);
                    continue;
                }
                node.outcome = SearchResult::Complete;
            }

            if (*node.outcome == SearchResult::Stop) {
                // Back out of every node, but without the proof logging that
                // finish_node() does: the proof is being abandoned.
                while (! _path.empty())
                    leave_node();
                return SearchResult::Stop;
            }

            auto result = finish_node(node);
            leave_node();
            if (_path.empty())
                return result;

            auto & parent = _path.back();
            if (result == SearchResult::RestartCutoffHit)
                parent.outcome = SearchResult::RestartCutoffHit;
            else {
                // Complete: this sibling's subtree was refuted under the
                // current path, so record it for restart-nogood learning. The
                // parent's iterator is still on the branch that led here.
                if (_learned_nogoods)
                    parent.refuted_siblings.push_back(*parent.branching->next);
                ++parent.branching->next;
            }
        }
    }

    /**
     * Push a node onto the path, propagate, and see what it holds: a dead end,
     * a solution, or something to branch on. Anything but the last sets the
     * node's outcome.
     */
    auto DepthFirstSearch::enter_node(
        const optional<Literal> & guess, const optional<Timestamp> & before_guess, vector<IntegerVariableCondition> && reduced_prefix) -> void
    {
        unsigned long long depth = _path.size();
        // At the root, whether a solution has been found carries over from
        // earlier passes: it decides which clause set later backtracks go into.
        auto & node = _path.emplace_back(before_guess, std::move(reduced_prefix), 0 == depth && found_solution);

        _stats.max_depth = max(_stats.max_depth, depth);
        ++_stats.recursions;

        if (_logger)
            _logger->enter_proof_level(depth + 1);

        if (_restart.conflicts_since_restart >= _restart.cutoff) {
            // This run has spent its conflict budget: abandon the tree and unwind
            // to the root for a restart. Unlike Stop this goes through the
            // backtrack/forget logging in finish_node(), at this and every
            // ancestor node, so the proof stays balanced and the restart can
            // continue it.
            node.outcome = SearchResult::RestartCutoffHit;
            return;
        }

        bool objective_failure = false;
        Literals guesses;
        if (guess)
            guesses.push_back(*guess);
        if (auto objective = _problem.optional_objective(); objective && objective_value) {
            auto objective_bound = objective->direction == ObjectiveDirection::Minimise ? objective->variable < *objective_value
                                                                                        : objective->variable >= *objective_value + 1_i;
            switch (_state.infer(objective_bound)) {
            case Inference::Contradiction: objective_failure = true; break;
            case Inference::NoChange: break;
            // The branch-and-bound bound tightened the objective variable, so seed the queue with
            // its propagators too. Without this only the node's guess seeds the queue, and a
            // propagator that would react to the new objective bound is not re-run here (issue #418).
            case Inference::BoundsChanged:
            case Inference::InteriorValuesChanged:
            case Inference::Instantiated: guesses.push_back(objective_bound); break;
            }
        }

        if (objective_failure || ! _propagators.propagate(guesses, _state, _logger, _optional_abort_flag)) {
            // A dead end: either the objective bound or a propagator wiped out
            // a domain. That is one conflict spent against the restart budget.
            ++_restart.conflicts_since_restart;
            node.outcome = SearchResult::Complete;
            return;
        }

        if (aborted()) {
            node.outcome = SearchResult::Stop;
            return;
        }

        // The root fixpoint holds under no decision, so from here on a
        // reason need not restate it. Its lines are at this node's
        // level, which is also what forgets the assumption.
        if (_logger && 0 == depth)
            _logger->assume_current_bounds(_state);

        node.branching.emplace(_branch_callback(_current_state, _propagators));

        if (node.branching->exhausted()) {
            node.outcome = record_solution(node) ? SearchResult::Complete : SearchResult::Stop;
            return;
        }

        if ((_callbacks.trace && ! _callbacks.trace(_state.current())) || aborted())
            node.outcome = SearchResult::Stop;
    }

    /**
     * Everything is assigned at this node. Returns false if the solution
     * callback says to stop.
     */
    auto DepthFirstSearch::record_solution(SearchNode & node) -> bool
    {
        if (_logger) {
            vector<pair<IntegerVariableID, Integer>> vars_and_values;
            for (const auto & v : _problem.all_normal_variables())
                vars_and_values.emplace_back(v, _state(v));
            _logger->solution(vars_and_values,
                _problem.optional_objective().transform([&](const Objective & objective) { return pair{objective, _state(objective.variable)}; }));
        }

        if (auto objective = _problem.optional_objective())
            objective_value = _state(objective->variable);

        ++_stats.solutions;
        ++number_of_solutions;
        node.contains_solution = true;
        found_solution = true;

        // Continuing past a solution while restarting is sound: the
        // proof's solx excludes each solution, so a fully-explored
        // subtree (solutions and all) is refuted and the nld nogood
        // learned for it stops a later pass re-entering and re-counting
        // it. So enumeration accumulates each solution exactly once.
        return ! _callbacks.solution || _callbacks.solution(_state.current());
    }

    /**
     * Take the node's next branch: guess it, and enter the child that gives.
     * This pushes onto the path, so the reference to the node is dead after.
     */
    auto DepthFirstSearch::branch(SearchNode & node) -> void
    {
        IntegerVariableCondition guess = *node.branching->next;

        // Reduced nld-nogoods thread down only the *positive* branch
        // decisions. A binary branch's second sibling is the negation of
        // its first (x=v then x!=v, or x<=v then x>v): descending into it
        // is a refutation flip --- a negative decision --- so it is
        // dropped, because the first sibling's own recorded nogood
        // re-derives it on the next pass. Every other descended sibling
        // (a first sibling, or any d-way value) is a free positive
        // decision and extends the prefix.
        //
        // Only maintain the reduced prefix when we are actually
        // learning nogoods: otherwise reduced_prefix stays empty and
        // the copy is free, so ordinary search pays nothing.
        auto child_prefix = node.reduced_prefix;
        if (_learned_nogoods) {
            bool negative_flip = node.sibling_index == 1 && node.first_sibling && guess == ! *node.first_sibling;
            if (! negative_flip)
                child_prefix.push_back(guess);
            if (node.sibling_index == 0)
                node.first_sibling = guess;
            ++node.sibling_index;
        }

        if (aborted()) {
            node.outcome = SearchResult::Stop;
            return;
        }

        auto before_guess = _state.new_epoch();
        _state.guess(guess);
        enter_node(guess, before_guess, std::move(child_prefix));
    }

    /**
     * The proof logging for leaving a node that is finished with, other than
     * by stopping: learned restart nogoods, then the backtrack.
     */
    auto DepthFirstSearch::finish_node(SearchNode & node) -> SearchResult
    {
        unsigned long long depth = _path.size() - 1;
        auto result = *node.outcome;

        // Whether the clause refuting this subtree has to go into VeriPB's core
        // set. It does exactly when the level we are about to forget can hold a
        // core constraint of its own, and there are only two things that put one
        // there: a `solx` blocking clause, recorded by a solution leaf at the
        // level it was found at, and the backtrack clause of a child that
        // needed to be in core for the same reason. Both happen if and only if a
        // solution was found somewhere under here, which is what
        // node.contains_solution says. An optimisation problem logs
        // `soli` rather than `solx` and deletes its superseded bounds by hand,
        // so nothing core ever lands at a search level and no clause here needs
        // promoting.
        auto backtrack_clause_set = (node.contains_solution && ! _problem.optional_objective()) ? ClauseSet::Core : ClauseSet::Derived;

        // Restart-nogood learning: each sibling refuted at this node before the
        // cutoff yields a reduced nld-nogood --- the positive decisions on the path
        // to here (reduced_prefix) plus that refuted decision. The clause drops the
        // negative (refutation-flip) path decisions but is still RUP: this is logged
        // during the deep-first unwind, when the ancestor nodes' backtrack lemmas
        // (which force exactly those dropped negatives) are still live below Top, so
        // RUP re-derives them. We derive it at Top so it survives the forget below
        // and the whole restart, and feed it to the store for the next pass.
        if (_learned_nogoods && result == SearchResult::RestartCutoffHit && ! node.refuted_siblings.empty()) {
            for (const auto & sibling : node.refuted_siblings) {
                // The proof line goes out for every refuted sibling, whatever
                // shape its decision has. On this path the node is about to
                // throw away the level below it without deriving a backtrack
                // clause of its own, so when that level holds a core constraint
                // --- a `solx` blocking clause, or a child's promoted backtrack
                // clause --- this nogood is the only thing left that implies it,
                // and skipping one would leave a deletion with nothing to check
                // it against. It does imply it: dropping the refutation-flip
                // decisions makes the nogood a subset of that sibling's
                // backtrack clause.
                if (_logger) {
                    vector<Literal> decisions;
                    decisions.reserve(node.reduced_prefix.size() + 1);
                    for (const auto & cond : node.reduced_prefix)
                        decisions.push_back(cond);
                    decisions.push_back(sibling);
                    _logger->emit_learned_nogood(decisions, backtrack_clause_set);
                }

                // The store holds plain conditions, so a sibling that is not one
                // (a proof-scaffolding literal) is not something it can record.
                auto sibling_cond = std::get_if<IntegerVariableCondition>(&sibling);
                if (! sibling_cond)
                    continue;
                Nogood nogood = node.reduced_prefix;
                nogood.push_back(*sibling_cond);
                _learned_nogoods->add(move(nogood));
            }
        }

        if (_logger) {
            _logger->enter_proof_level(depth);
            if (result == SearchResult::RestartCutoffHit) {
                // We must NOT delete the root node's own guess-independent
                // propagation (proof level 1): the next pass starts from the same
                // root fixpoint, so propagate() re-emits nothing there, and that
                // reasoning has to survive for the next pass's backtracks to remain
                // RUP. So at the root (depth 0) we keep level 1; deeper
                // guess-dependent levels are re-derived next pass.
                if (depth > 0)
                    _logger->forget_proof_level(depth + 1);
            }
            else {
                // A normal backtrack: the subtree under these guesses was refuted,
                // so we may assert the negation of the guess set (RUP from the
                // refutation that the forget below then discards).
                vector<Literal> guesses;
                for (const auto & g : _state.guesses())
                    guesses.push_back(g);
                _logger->backtrack(guesses, backtrack_clause_set);
                _logger->forget_proof_level(depth + 1);
            }
        }

        return result;
    }

    /**
     * Pop the node at the end of the path, and return its parent to the state
     * it was in before guessing it.
     */
    auto DepthFirstSearch::leave_node() -> void
    {
        auto before_guess = _path.back().before_guess;
        bool contains_solution = _path.back().contains_solution;
        _path.pop_back();

        if (! _path.empty()) {
            auto & parent = _path.back();
            if (contains_solution)
                parent.contains_solution = true;
            else
                ++_stats.failures;
            _state.backtrack(*before_guess);
        }
    }
}

auto gcs::solve_with(
    Problem & problem, SolveCallbacks callbacks, const optional<ProofOptions> & optional_proof_options, atomic<bool> * optional_abort_flag) -> Stats
{
    Stats stats;

    // Before anything can report: a presolver's decision is said as it is made,
    // and the presolvers run inside this call. Unset does not mean silence
    // here, deliberately --- see SolveCallbacks::stats_report.
    stats.set_report_handler(callbacks.stats_report ? callbacks.stats_report : default_stats_report());

    auto start_time = steady_clock::now();

    optional<Proof> optional_proof;
    if (optional_proof_options) {
        optional_proof.emplace(*optional_proof_options);
    }

    auto state = problem.create_state_for_new_search(optional_proof ? optional_proof->model() : nullptr);

    if (optional_proof) {
        if (auto objective = problem.optional_objective())
            optional_proof->model()->set_objective(*objective);

        optional_proof->model()->preserve(problem.all_normal_variables());

        // Every variable the objective and preserve list mention now exists,
        // so the OPB front matter can go out; the constraint definitions that
        // follow stream straight to the file.
        optional_proof->model()->write_preamble();
    }

    auto propagators = problem.create_propagators(state, stats, optional_proof ? optional_proof->model() : nullptr);

    // With restarts on, search learns nogoods from refuted regions. Install an
    // (initially empty) Nogoods over a store the restart loop grows, subscribed
    // to every variable since a later-learned nogood may mention any. This is
    // engine-owned, not user-posted --- restart nogoods are internal (and, under
    // parallel search, per-thread). Must follow create_propagators (it installs
    // into them) and precede the model finalise below; any model definitions it
    // adds land after the preamble, like every other constraint's.
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
        auto nogoods_constraint = nogoods_over_learned_store(nogood_store, problem.all_normal_variables(), refined_nogoods);
        nogoods_constraint.set_constraint_id(NamedConstraint{"learned_nogoods"});
        std::move(nogoods_constraint).install(propagators, state, optional_proof ? optional_proof->model() : nullptr);
    }

    if (optional_proof) {
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

            // Whatever that presolver installed gets initialised before the
            // next one looks at the problem. A presolver can install a
            // constraint, and a constraint can install an initialiser --- that
            // is where one introduces a proof-only variable, for instance ---
            // so without this the constraint would be propagating against
            // definitions that were never written, which shows up as a
            // rejected proof at best. initialise() picks up where it left off,
            // so the first round's initialisers do not run again.
            if (! propagators.initialise(state, optional_proof ? optional_proof->logger() : nullptr)) {
                presolve_success = false;
                break;
            }
        }
    }

    // Now that nothing more will be installed, decide which optional interior
    // prunings anything could observe, and switch the rest to their fallbacks
    // (dev_docs/optional-interior-pruning.md). Not before: a presolver can
    // install a constraint whose propagation is affected by holes nothing else
    // was affected by. Anything that propagated before here, a presolver's
    // probing say, ran with every pruning on, which is only ever stronger. The
    // encoding is unaffected either way, having been written when the
    // constraints were installed.
    if (presolve_success)
        propagators.choose_optional_interior_pruning();

    // The best value the objective could take, as of the root: what a proof
    // that ends without proving optimality can still claim as its bound.
    Integer objective_root_bound_for_proof = 0_i;
    if (auto objective = problem.optional_objective(); optional_proof && objective)
        objective_root_bound_for_proof =
            objective->direction == ObjectiveDirection::Minimise ? state.lower_bound(objective->variable) : state.upper_bound(objective->variable);

    if (initialisation_success && presolve_success) {
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

        DepthFirstSearch search{problem, propagators, state, stats, callbacks, branch_callback, optional_proof ? optional_proof->logger() : nullptr,
            nogood_store.get(), restart, optional_abort_flag};

        SearchResult search_result;
        do {
            restart.conflicts_since_restart = 0;
            search_result = search.run_pass();

            if (search_result == SearchResult::RestartCutoffHit) {
                ++stats.restarts;
                for (auto & observer : propagators.conflict_observers())
                    observer->on_restart();
                restart_schedule->advance();
                restart.cutoff = restart_schedule->current_cutoff();

                // A pass that ends at its cutoff reads the abort flag only if
                // it propagated somewhere first, so check it here too rather
                // than rely on every pass doing so (#1391). The proof is
                // balanced at the root, so stopping here concludes as any
                // other abort does.
                if (optional_abort_flag && optional_abort_flag->load())
                    search_result = SearchResult::Stop;
            }
        } while (search_result == SearchResult::RestartCutoffHit);

        if (search_result == SearchResult::Complete) {
            if (optional_proof) {
                if (auto objective = problem.optional_objective()) {
                    if (search.objective_value)
                        optional_proof->logger()->conclude_optimality(*objective, *search.objective_value);
                    else
                        optional_proof->logger()->conclude_unsatisfiable(true);
                }
                else if (search.found_solution) {
                    optional_proof->logger()->conclude_complete_enumeration(search.number_of_solutions);
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
                if (auto objective = problem.optional_objective()) {
                    if (search.objective_value)
                        optional_proof->logger()->conclude_bounds(*objective, objective_root_bound_for_proof, *search.objective_value);
                    else
                        optional_proof->logger()->conclude_none();
                }
                else if (search.found_solution)
                    optional_proof->logger()->conclude_satisfiable();
                else
                    optional_proof->logger()->conclude_none();
            }
        }
    }
    else {
        if (optional_proof)
            optional_proof->logger()->conclude_unsatisfiable(problem.optional_objective().has_value());
        if (callbacks.completed)
            callbacks.completed();
    }

    if (optional_proof)
        optional_proof->model()->names_and_ids_tracker().finalise();

    stats.solve_time = duration_cast<microseconds>(steady_clock::now() - start_time);
    propagators.fill_in_constraint_stats(stats);
    if (nogood_store)
        stats.learned_nogoods = nogood_store->size();

    // The search is over, so a caller holding the result should not be holding
    // a live callback into it: the notes are all accumulated, and reporting a
    // new one now would be reporting it about nothing.
    stats.set_report_handler(StatsReportCallback{});

    return stats;
}

auto gcs::solve(Problem & problem, SolutionCallback callback, const optional<ProofOptions> & proof_options) -> Stats
{
    return solve_with(problem, SolveCallbacks{.solution = callback}, proof_options);
}
