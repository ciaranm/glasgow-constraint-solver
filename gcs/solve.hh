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
#include <variant>
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
     * \defgroup BranchDecisions Branch decisions and their backtrack advances
     *
     * A branching generator yields BranchDecision instances. Each pairs the
     * IntegerVariableCondition to branch on (the \c guess) with a declaration of
     * how the node's backtrack constraint tightens once that decision's subtree
     * is refuted (the \c on_refuted BacktrackAdvance). The framework folds those
     * advances; branchers never write raw proof bookkeeping.
     *
     * \ingroup SolveCallbacks
     */

    /**
     * \brief The backtrack-advance kinds a BranchDecision can declare.
     *
     * \ingroup BranchDecisions
     */
    namespace backtrack_advance
    {
        /**
         * \brief Refuting this decision's subtree entails a new lower bound on
         * \c var: the node's backtrack constraint tightens to \c var >= (next
         * live threshold), naming ONE order literal.
         */
        struct LowerBound final
        {
            IntegerVariableID var;
        };

        /**
         * \brief Symmetric to LowerBound: refuting entails \c var <= (next live
         * threshold), i.e. \c var < t.
         */
        struct UpperBound final
        {
            IntegerVariableID var;
        };

        /**
         * \brief The generic fallback: accumulate \c !guess into the node's
         * excluded set. This is exactly today's \c ~(all guesses) backtrack
         * clause; it names a growing set, so nothing is deletable for that
         * variable. The default advance.
         */
        struct Exclude final
        {
        };

        /**
         * \brief Escape hatch for exotic branchers that prove their own backtrack
         * constraint.
         *
         * Placeholder for now: the design's sketched WPBSum callback is "not
         * fleshed out until a use case appears" (dev-doc "Extensibility"), and
         * spelling it would drag the proof-innards WPBSumLE type into this public
         * header. Stage A ships an empty struct so BacktrackAdvance's variant is
         * exhaustive and compiles; nothing constructs it yet.
         */
        struct Custom final
        {
        };
    }

    /**
     * \brief How a BranchDecision's backtrack constraint tightens when its
     * subtree is refuted.
     *
     * \ingroup BranchDecisions
     */
    using BacktrackAdvance =
        std::variant<backtrack_advance::LowerBound, backtrack_advance::UpperBound, backtrack_advance::Exclude, backtrack_advance::Custom>;

    /**
     * \brief A single branching decision: what to branch on, plus how the node's
     * backtrack constraint advances if that decision's subtree is refuted.
     *
     * An IntegerVariableCondition converts implicitly to a BranchDecision
     * defaulting to backtrack_advance::Exclude, so an existing branch generator
     * that yields bare conditions keeps compiling and, under the default advance,
     * keeps its proof byte-identical.
     *
     * \ingroup BranchDecisions
     */
    struct BranchDecision final
    {
        IntegerVariableCondition guess;                             ///< What to branch on.
        BacktrackAdvance on_refuted = backtrack_advance::Exclude{}; ///< How the node advances if refuted.

        BranchDecision(IntegerVariableCondition c) : guess(c)
        {
        }

        BranchDecision(IntegerVariableCondition c, BacktrackAdvance a) : guess(c), on_refuted(a)
        {
        }
    };

    /**
     * \brief Called by gcs::solve_with() to determine branching when
     * searching, should return a generator of BranchDecision instances (each
     * carrying an IntegerVariableCondition, which may be a range condition for
     * interval accept/reject branching) that corresponds to a complete branching
     * choice, or that yields nothing if every variable is instantiated.
     *
     * \warning The CurrentState and Propagators references are into live
     * solver internals, and are valid only for the duration of the call.
     *
     * \ingroup SolveCallbacks
     * \sa SearchHeuristics
     */
    using BranchCallback = std::function<std::generator<BranchDecision>(const CurrentState &, const innards::Propagators &)>;

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
