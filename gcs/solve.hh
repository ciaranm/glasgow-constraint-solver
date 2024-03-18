#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SOLVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SOLVE_HH

#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/proof.hh>
#include <gcs/stats.hh>

#include <atomic>
#include <functional>
#include <vector>

namespace gcs
{
    /**
     * \defgroup SolveCallbacks Callbacks for solving
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
     * \brief Called by gcs::solve_with() to determine the branch variable when
     * searching, should return nullopt if every variable is instantiated.
     *
     * \ingroup SolveCallbacks
     * \sa SearchHeuristics
     */
    using BranchCallback = std::function<auto(const CurrentState &, const innards::Propagators &)->std::optional<IntegerVariableID>>;

    /**
     * \brief Called by gcs::solve_with() when branching on the specified
     * variable, should return a vector of conditions that describe a complete
     * branching choice.
     *
     * \ingroup SolveCallbacks
     * \sa SearchHeuristics
     */
    using GuessCallback = std::function<auto(const CurrentState &, IntegerVariableID)->std::vector<IntegerVariableCondition>>;

    /**
     * \brief Called by gcs::solve_with() after the proof has been started.
     *
     * \ingroup SolveCallbacks
     */
    using AfterProofStartedCallback = std::function<auto(const CurrentState &)->void>;

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
        BranchCallback branch = BranchCallback{};
        GuessCallback guess = GuessCallback{};
        AfterProofStartedCallback after_proof_started = AfterProofStartedCallback{};
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
