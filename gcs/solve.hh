#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SOLVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SOLVE_HH

#include <gcs/current_state.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/problem.hh>
#include <gcs/proof.hh>
#include <gcs/restarts.hh>
#include <gcs/stats.hh>
#include <gcs/variable_condition.hh>

#include <optional>

#include <atomic>
#include <functional>
#include <version>

#ifdef __cpp_lib_generator
#include <generator>
#else
#include <__generator.hpp>
#endif

namespace gcs
{
    /**
     * \defgroup SolveCallbacks Callbacks for solving
     *
     * \warning The references passed to a callback are valid only for the
     * duration of that call, and must not be stored for later use. Use
     * CurrentState::clone() if you need to save a state.
     *
     * \sa SearchHeuristics
     */

    /**
     * \brief Called for every solution found when using gcs::solve() and gcs::solve_with(),
     * if false is returned then no further solutions will be given.
     *
     * \ingroup SolveCallbacks
     */
    using SolutionCallback = std::function<auto(const CurrentState &)->bool>;

    /**
     * \brief Called after propagation is complete when using gcs::solve_with(),
     * if false is returned then search will stop.
     *
     * \ingroup SolveCallbacks
     */
    using TraceCallback = std::function<auto(const CurrentState &)->bool>;

    /**
     * \brief Called by gcs::solve_with() to determine branching when
     * searching, should return a generator of IntegerVariableCondition
     * instances (which may be range conditions, for interval accept/reject
     * branching) that corresponds to a complete branching choice, or that
     * yields nothing if every variable is instantiated.
     *
     * \warning The CurrentState and Propagators references are into live
     * solver internals, and are valid only for the duration of the call.
     *
     * \ingroup SolveCallbacks
     * \sa SearchHeuristics
     */
    using BranchCallback = std::function<std::generator<IntegerVariableCondition>(const CurrentState &, const innards::Propagators &)>;

    /**
     * \brief The branching heuristic for gcs::solve_with(): given a search's
     * Problem, State, and Propagators, it does any one-time per-search setup and
     * returns the per-node BranchCallback to branch with.
     *
     * solve_with() calls it exactly once, after propagators are built, so a
     * stateful heuristic (for example dom/wdeg) can construct its state and
     * attach itself as a conflict observer before search begins; the returned
     * BranchCallback is then reused at every node. A stateless heuristic ignores
     * the arguments and returns its callback. gcs::branch_with() produces one of
     * these from a gcs::variable_order:: heuristic and a gcs::value_order::
     * generator.
     *
     * \ingroup SolveCallbacks
     * \sa SearchHeuristics
     */
    using BranchHeuristic = std::function<BranchCallback(const Problem &, innards::State &, innards::Propagators &)>;

    /**
     * \brief Called by gcs::solve_with() after the proof has been started.
     *
     * \ingroup SolveCallbacks
     */
    using AfterProofStartedCallback = std::function<auto(const CurrentState &)->void>;

    /**
     * \brief Called by gcs::solve_with() after the solve has completed successfully (not
     * aborted due to a callback returning false, or the abort flag being set).
     *
     * \ingroup SolveCallbacks
     */
    using CompletedCallback = std::function<auto()->void>;

    /**
     * \brief Callbacks for gcs::solve_with().
     *
     * Every callback is optional.
     *
     * \ingroup SolveCallbacks
     */
    struct SolveCallbacks final
    {
        SolutionCallback solution = SolutionCallback{};
        TraceCallback trace = TraceCallback{};
        BranchHeuristic branch = BranchHeuristic{};
        AfterProofStartedCallback after_proof_started = AfterProofStartedCallback{};
        CompletedCallback completed = CompletedCallback{};

        /**
         * \brief If set, search restarts on a growing sequence of conflict
         * cutoffs instead of running a single depth-first pass.
         *
         * Default (unset) reproduces a single, exhaustive depth-first search.
         * \warning Sound only for finding one solution or for optimising; see
         * gcs::RestartSchedule.
         */
        std::optional<RestartSchedule> restarts = std::nullopt;
    };

    /**
     * \brief Solve a problem, and call the provided callback for each solution
     * found.
     *
     * If the callback returns false, no further solutions will be provided. If
     * we are dealing with an optimisation problem, the callback will be called
     * for every candidate solution, not just an optimal solution.
     *
     * \ingroup Core
     * \sa SolveCallbacks
     */
    auto solve(Problem &, SolutionCallback callback, const std::optional<ProofOptions> & = std::nullopt) -> Stats;

    /**
     * \brief Solve a problem, with callbacks for various events.
     *
     * All callback members are optional. If a solution or trace callback
     * returns false, no further solutions will be provided.
     *
     * If the final argument is not nullptr, the provided atomic might be
     * polled and search might abort if it becomes true.
     *
     * \ingroup Core
     * \sa SolveCallbacks
     */
    auto solve_with(Problem &, SolveCallbacks callbacks, const std::optional<ProofOptions> & = std::nullopt,
        std::atomic<bool> * optional_abort_flag = nullptr) -> Stats;
}

#endif
