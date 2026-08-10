#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_SIMPLIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_SIMPLIFY_HH

#include <gcs/integer.hh>
#include <gcs/stats.hh>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief What the difference-logic root simplification stage did, filled in
     * the first time the propagator runs.
     *
     * A simplification stage that silently does nothing preserves the solution
     * set, adds no OPB content, leaves every proof verifying and leaves every
     * search tree unchanged --- so it passes every check there is. These counters
     * are how a test tells "working" from "no-op", and every one of them is
     * asserted on somewhere in `difference_constraints_test.cc` or
     * `difference_logic_test.cc`. Do not turn them into decoration.
     *
     * \sa DifferenceConstraints::simplifying_at_root
     * \ingroup Constraints
     */
    struct DifferenceSimplificationStats final : ComponentStats
    {
        /// True if the stage actually ran. It runs once, from an initialiser,
        /// which is the root by construction (see
        /// `dev_docs/difference-logic.md`).
        bool ran = false;

        /// How many times the Johnson's pass was repeated. Fixing a condition
        /// false can make its complement definitely true, which adds an edge to
        /// the base graph and can license further fixing, so the stage iterates
        /// to a fixpoint exactly as the paper's section 5.3 does. One round means
        /// nothing was fixed.
        std::size_t rounds = 0;

        /// Nodes and edges the stage was handed.
        ///@{
        std::size_t nodes = 0;
        std::size_t edges = 0;
        std::size_t conditional_edges = 0;
        ///@}

        /// Edges dropped from the propagator's *internal* graph because a
        /// strictly shorter path already implies them (or because they duplicate
        /// another edge attaining the same distance). The model keeps them: this
        /// is a decision about what to propagate, not about what the model says,
        /// and so it has no proof obligation at all.
        std::size_t redundant_edges_removed = 0;

        /// Of those, how many carried a condition. A conditional edge is dropped
        /// on the weaker test `d >= D_uv`, since an implied edge that merely
        /// restates a distance the base graph already has cannot ever add
        /// anything.
        std::size_t redundant_conditional_edges_removed = 0;

        /// Conditional edges dropped because their condition is already
        /// definitely false, so the edge can never participate again.
        std::size_t dead_edges_removed = 0;

        /// Conditions fixed false because activating their edge would close a
        /// negative cycle. This is the sub-step that carries a proof obligation,
        /// and the one the paper's RCPSP/max unsatisfiability headline belongs
        /// to.
        std::size_t conditions_fixed = 0;

        /// Nodes left with no incident edge once the above was done, and so
        /// dropped from the relaxation loop and from the round bound.
        std::size_t isolated_nodes_removed = 0;

        /// Zero-weight cycles found, and how many nodes lie on one. Unifying
        /// those nodes is the paper's fourth sub-step, which is *not*
        /// implemented; these are reported so that the question of whether it
        /// would ever fire on a real model is answered with a measurement rather
        /// than a guess. \sa dev_docs/difference-logic.md
        ///@{
        std::size_t zero_weight_cycles = 0;
        std::size_t nodes_on_zero_weight_cycles = 0;
        ///@}

        /// True if the base graph was found to contain a negative cycle while
        /// simplifying. The stage then stops and leaves the refutation to the
        /// propagator's own Bellman-Ford pass, which has the cycle extraction and
        /// the proof shape for it.
        bool base_negative_cycle = false;

        /// Wall-clock seconds the stage cost, summed over its rounds. Reported
        /// separately from the solve time because it is a one-off cubic-ish price
        /// paid at the root, and the paper is explicit that it should be judged
        /// on its own.
        double seconds = 0.0;

        /**
         * \brief `difference_logic_simplify`, which is what a report has called
         * this stage since before it was a ComponentStats.
         *
         * Not `difference_simplify` after the header, as the ComponentStats
         * convention would otherwise have it. The names this feeds are already
         * public --- `minizinc/CMakeLists.txt` pins
         * `differenceLogicSimplifyRan` --- and a stage that reports under two
         * different names across a version is worse than one whose identifier
         * does not match its filename.
         */
        [[nodiscard]] auto component_name() const -> std::string override;
        [[nodiscard]] auto summary() const -> std::string override;

        /**
         * \brief Every field, with \ref seconds rendered as whole milliseconds
         * under the name `milliseconds`.
         *
         * A StatsEntry is an integer, and a duration is the one field here that
         * is not. Milliseconds rather than truncated seconds because a stage
         * that costs 900ms is worth telling apart from one that costs nothing,
         * and `seconds=0` would not.
         */
        [[nodiscard]] auto entries() const -> std::vector<StatsEntry> override;
    };
}

namespace gcs::innards
{
    /**
     * \brief What part an edge plays in one round of the simplification.
     *
     * \sa simplify_difference_graph
     * \ingroup Innards
     */
    enum class DifferenceSimplifyRole
    {
        /// In the base graph: unconditional, or conditional on something that is
        /// currently definitely true. Distances are computed over exactly these.
        Base,

        /// Conditional on something undecided. Not in the base graph, but a
        /// candidate for having its condition fixed false.
        Candidate,

        /// Conditional on something definitely false. Not in the graph and never
        /// will be.
        Ignored
    };

    /**
     * \brief One edge as the simplification pass sees it: `from - to <= d` over
     * node indices, with no notion of what constraint it came from.
     *
     * \sa simplify_difference_graph
     * \ingroup Innards
     */
    struct DifferenceSimplifyEdge
    {
        std::size_t from;
        std::size_t to;
        Integer d;
    };

    /**
     * \brief What one round of simplification concluded.
     *
     * \sa simplify_difference_graph
     * \ingroup Innards
     */
    struct DifferenceSimplifyOutcome
    {
        /// The base graph has a negative cycle, so it is already infeasible and
        /// nothing else here is filled in. The caller refutes; this pass does not
        /// carry the cycle-extraction machinery.
        bool base_negative_cycle = false;

        /// Parallel to the edge list: this edge may be dropped from the internal
        /// graph without weakening propagation.
        std::vector<bool> remove;

        /// Candidate edges whose condition must be false, each with the witness
        /// path: a list of edge indices forming a path from the candidate's `to`
        /// back to its `from`, so that the candidate edge followed by the path is
        /// a cycle of strictly negative weight.
        std::vector<std::pair<std::size_t, std::vector<std::size_t>>> fix;

        /// Zero-weight cycles found in the base graph, and how many nodes lie on
        /// one.
        ///@{
        std::size_t zero_weight_cycles = 0;
        std::size_t nodes_on_zero_weight_cycles = 0;
        ///@}
    };

    /**
     * \brief One round of the paper's root simplification: Johnson's all-pairs
     * shortest paths over the base graph, then redundant-edge detection,
     * condition fixing, and zero-weight-cycle detection.
     *
     * This is a pure function of the graph. It reads no state, makes no
     * inference, emits no proof line and allocates nothing that outlives it,
     * which is what makes it the same code for a posted DifferenceConstraints and
     * for a presolver-built system, and what makes it directly unit-testable.
     *
     * Bellman-Ford from the paper's imaginary source `v0` (a zero-weight edge to
     * every node) gives the potentials, `n` Dijkstras on the reduced-cost graph
     * give the distances. That is `O(n^2 log n + nm)`, paid once.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto simplify_difference_graph(std::size_t number_of_nodes, const std::vector<DifferenceSimplifyEdge> & edges,
        const std::vector<DifferenceSimplifyRole> & roles) -> DifferenceSimplifyOutcome;
}

#endif
