#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_INCREMENTAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_INCREMENTAL_HH

#include <gcs/integer.hh>

#include <cstddef>
#include <optional>
#include <utility>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief One edge of a difference system as the propagator's hot loops see
     * it: `arcs[from] - arcs[to] <= d`, derived from the \c posted_index th
     * constraint the caller handed over.
     *
     * The *size* of this is a measurable property rather than a detail: the
     * from-scratch Bellman-Ford pass scans the whole array once per round.
     * Carrying an `optional<IntegerVariableCondition>` inline took it from 32
     * bytes to 96 and cost 2.9x on `examples/difference_chain` at `n = 640`,
     * with the propagation and recursion counts unchanged --- i.e. pure memory
     * traffic in the innermost loop. So DifferenceGraphEdge stays the convenient
     * *construction* type, with the condition attached to the edge it belongs
     * to, and install_difference_propagator repacks it once into this plus a
     * parallel condition array read only on the cold paths.
     *
     * \ingroup Innards
     */
    struct DifferenceArc
    {
        std::size_t from;
        std::size_t to;
        Integer d;
        std::size_t posted_index;
    };

    static_assert(sizeof(DifferenceArc) <= 32, "the difference-logic relaxation loop scans this array once per round; keep it small");

    /**
     * \brief Whether the shared propagator runs the incremental algorithms, and
     * whether it audits them against the from-scratch pass.
     *
     * The from-scratch Bellman-Ford version stays compiled and selectable for
     * two reasons, and both are about the fact that **every incrementality bug
     * is invisible to proof logging**: a proof certifies what was derived, so a
     * *lost* inference passes VeriPB silently.
     *
     * - \c enabled off gives a trusted reference implementation, against which
     *   `recursions` and the solution sequence must come out **identical** ---
     *   given the gate invariants the incremental version reaches the same
     *   per-call fixpoint, and a bounds fixpoint is unique, so the search tree
     *   cannot legitimately move. (`propagations`, other propagators' wake order
     *   and proof bytes may differ: Dijkstra settles in a different order from
     *   the predecessor forest.)
     * - \c audit re-runs the from-scratch pass after *every* incremental call,
     *   on the same starting bounds and the same active edge set, and requires
     *   the two to agree node for node. That catches a completeness failure at
     *   the wake where it first occurs, which is the only way to catch a stale
     *   `Do` array, a stale potential function, a missed activation seed or a
     *   wrong `pi(v0)`.
     *
     * \c audit is also forced on by the `GCS_DIFFERENCE_AUDIT` environment
     * variable, so a whole corpus can be run under it without touching any
     * model.
     *
     * \sa install_difference_propagator
     * \ingroup Innards
     */
    struct DifferenceIncrementalOptions
    {
        bool enabled = true;
        bool audit = false;
    };

    /**
     * \brief Compressed adjacency over a fixed arc array: `arcs[start[v]]` up to
     * `arcs[start[v + 1]]` are the indices of the arcs incident to \c v at the
     * chosen end.
     *
     * Dijkstra needs adjacency where Bellman-Ford needed only a flat scan, and
     * the adjacency is over *all* arcs, with the currently active ones selected
     * by a flag array as they are traversed. That keeps it a build-once
     * structure even though the active set changes on every wake.
     *
     * \ingroup Innards
     */
    struct DifferenceAdjacency
    {
        std::vector<std::size_t> start;
        std::vector<std::size_t> arcs;
    };

    /**
     * \brief Build adjacency grouped by each arc's tail (\c by_tail) or head.
     *
     * Lower bounds flow forwards along the arcs, so IncLB and IncSat want the
     * by-tail adjacency; upper bounds flow backwards, so IncUB wants the
     * by-head one.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto build_difference_adjacency(std::size_t number_of_nodes, const std::vector<DifferenceArc> & arcs, bool by_tail)
        -> DifferenceAdjacency;

    /**
     * \brief Whether \c active selects arc \c e. An empty \c active means every
     * arc is active, which is the shape an unconditional system takes.
     *
     * \ingroup Innards
     */
    [[nodiscard]] inline auto difference_arc_is_active(const std::vector<char> & active, std::size_t e) -> bool
    {
        return active.empty() || 0 != active[e];
    }

    /**
     * \brief A valid potential function for the active sub-graph, or nullopt if
     * that sub-graph has a negative cycle.
     *
     * Bellman-Ford from the paper's imaginary source `v0` with a zero-weight
     * edge to every node --- seeding every potential at zero *is* that source's
     * edge set --- so the result satisfies `pi(u) + d - pi(v) >= 0` for every
     * active arc `u --d--> v`, which is what makes the reduced-cost graph
     * non-negative and Dijkstra applicable.
     *
     * Paid once, at the propagator's first call. Every later change to the
     * active set goes through difference_repair_potential.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto difference_initial_potential(std::size_t number_of_nodes, const std::vector<DifferenceArc> & arcs,
        const std::vector<char> & active) -> std::optional<std::vector<Integer>>;

    /**
     * \brief Check the potential invariant over the active arcs. O(m), for the
     * audit and for assertions; nothing on a shipping path calls it.
     *
     * Returns the offending arc index, or nullopt if the potential is valid.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto difference_invalid_potential_arc(const std::vector<DifferenceArc> & arcs, const std::vector<char> & active,
        const std::vector<Integer> & potential) -> std::optional<std::size_t>;

    /**
     * \brief Scratch for difference_repair_potential, hoisted out so that a wake
     * allocates nothing.
     *
     * \ingroup Innards
     */
    struct DifferencePotentialWorkspace
    {
        std::vector<Integer> gamma;
        std::vector<Integer> updated;
        std::vector<char> is_updated;
        std::vector<std::size_t> touched;
        std::vector<std::pair<Integer, std::size_t>> heap;
    };

    /**
     * \brief IncSat: repair a valid potential function after one arc joins the
     * active set, or report that the active sub-graph now has a negative cycle.
     *
     * The paper's Algorithm 1, from Cotton and Maler. \c potential must be valid
     * for the active arcs *excluding* \c added_arc, and \c active must already
     * include \c added_arc. On \c true the potential is valid for the whole
     * active set; on \c false the caller must refute --- this function does not
     * extract the cycle, because the from-scratch pass already carries the
     * extraction and the telescoping `pol` that goes with it, and a negative
     * cycle ends the search anyway.
     *
     * Must be run on **every** activation, including re-activation after
     * backtracking. The potential is never trailed and drifts downwards over the
     * whole search, so an arc that was valid when it was last active may need
     * repair when it comes back: nothing may cache "this arc has been checked".
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto difference_repair_potential(std::size_t number_of_nodes, const std::vector<DifferenceArc> & arcs,
        const DifferenceAdjacency & by_tail, const std::vector<char> & active, std::vector<Integer> & potential, std::size_t added_arc,
        DifferencePotentialWorkspace & work) -> bool;

    /**
     * \brief Scratch and results for difference_incremental_bounds, hoisted out
     * so that a wake allocates nothing.
     *
     * \c settle_order is the output that matters: the nodes Dijkstra settled, in
     * the order it settled them. Each node's predecessor is settled before it,
     * so walking this order is exactly the order in which the bound pushes have
     * to be inferred for each to be able to cite the one before it.
     *
     * \ingroup Innards
     */
    struct DifferenceBoundsWorkspace
    {
        std::vector<Integer> gamma;
        std::vector<char> queued;
        std::vector<char> settled;
        std::vector<char> has_predecessor;
        std::vector<std::size_t> predecessor;
        std::vector<Integer> settled_bound;
        std::vector<std::size_t> settle_order;
        std::vector<std::pair<Integer, std::size_t>> heap;
    };

    /**
     * \brief IncLB: process every bound change since the last run in one
     * Dijkstra on the reduced-cost graph.
     *
     * The paper's Algorithm 3, transcribed from its Example 7's arithmetic
     * rather than from the pseudocode, whose lines 15-16 read `gamma(s)` after
     * line 10 has set it to `+infinity` and therefore never propagate anything.
     *
     * Everything is in *lower bound* orientation: arc `(s, t, d)` reads
     * `bound(t) >= bound(s) - d`, \c by_tail selects the by-tail adjacency, and
     * \c potential must satisfy `potential(s) + d - potential(t) >= 0`. IncUB is
     * the same function with the by-head adjacency and with the potential, the
     * bounds and the gate all negated by the caller, which is why there is only
     * one copy of this.
     *
     * \c gate is the paper's `Do`, the bounds the *previous* run propagated
     * from, and the two invariants on it are what make the pass complete:
     *
     * - I1, `gate(x) <= bound(x)` for every node;
     * - I2, `gate(t) >= gate(s) - d` for every currently active arc.
     *
     * \c forced marks nodes that must be seeded and expanded whatever the gate
     * says. That is how a newly activated arc gets its bound propagation: mark
     * its tail, and Dijkstra carries the tail's bound across the new arc and
     * onwards. The paper's section 4.4 says to do this and its section 5.4's
     * during-search description omits it; transcribing the latter alone loses
     * every push a reification delivers.
     *
     * On return \c work.settle_order holds the settled nodes in settle order,
     * \c work.settled_bound their new bounds, and \c work.predecessor the arc
     * each one's bound came across. The caller infers along \c settle_order and
     * then sets `gate(v) := settled_bound(v)` for every settled `v` --- which is
     * the bounds this run propagated *from*, and emphatically not the bounds the
     * state ends the call with: gcs domains have holes, an inferred bound can
     * snap above the value this pass computed, and recording the snapped value
     * would leave the mandatory self-re-wake with nothing in `Vl` and the
     * consequences of the snap silently lost.
     *
     * \ingroup Innards
     */
    auto difference_incremental_bounds(std::size_t number_of_nodes, const std::vector<DifferenceArc> & arcs, const DifferenceAdjacency & adjacency,
        bool by_tail, const std::vector<char> & active, const std::vector<Integer> & potential, const std::vector<Integer> & bound,
        const std::vector<Integer> & gate, const std::vector<char> & forced, DifferenceBoundsWorkspace & work) -> void;
}

#endif
