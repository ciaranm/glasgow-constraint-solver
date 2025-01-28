#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SOLVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SOLVE_HH

#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/proof.hh>
#include <gcs/stats.hh>

#include <atomic>
#include <functional>
#include <vector>

#if __has_cpp_attribute(__cpp_lib_generator)
#include <generator>
#else
#include <__generator.hpp>
#endif

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
     * \brief Called by gcs::solve_with() to determine branching when
     * searching, should return a generator of IntegerVariableCondition
     * instances that corresponds to a complete branching choice, or
     * that yields nothing if every variable is instantiated.
     *
     * \ingroup SolveCallbacks
     * \sa SearchHeuristics
     */
    using BranchCallback = std::function<std::generator<IntegerVariableCondition>(const CurrentState &, const innards::Propagators &)>;

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
        BranchCallback branch = BranchCallback{};
        AfterProofStartedCallback after_proof_started = AfterProofStartedCallback{};
        CompletedCallback completed = CompletedCallback{};
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
