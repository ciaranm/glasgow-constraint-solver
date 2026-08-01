#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_GRAPH_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_GRAPH_HH

#include <gcs/constraint_id.hh>
#include <gcs/constraints/difference/difference_simplify.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <memory>
#include <optional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief One edge of a canonicalised difference system: `nodes[from] -
     * nodes[to] <= d`, derived from the `posted_index`th constraint the caller
     * handed over.
     *
     * When \c cond is engaged the edge is *half-reified*: the constraint states
     * `cond -> nodes[from] - nodes[to] <= d`, and the edge takes part in the
     * graph only while \c cond currently holds. Its OPB row is emitted under
     * \c HalfReifyOnConjunctionOf, so it carries a big-M term on `~cond` which
     * survives every telescoping sum as a residual --- which is exactly the
     * clause the propagator wants to learn, and why \c cond must appear in the
     * reason of anything derived using this edge.
     *
     * \sa DifferenceGraph
     * \ingroup Innards
     */
    struct DifferenceGraphEdge
    {
        std::size_t from;
        std::size_t to;
        Integer d;
        std::size_t posted_index;
        std::optional<IntegerVariableCondition> cond = std::nullopt;
    };

    /**
     * \brief An edge with a constant operand, which is not a graph edge at all
     * but a plain bound on the other operand: `nodes[node] >= value` when
     * `is_lower`, `nodes[node] <= value` otherwise.
     *
     * A \c cond means the bound is only enforced while that condition holds, and
     * is then cited as the reason for applying it.
     *
     * \sa DifferenceGraph
     * \ingroup Innards
     */
    struct DifferenceStaticBound
    {
        std::size_t node;
        Integer value;
        bool is_lower;
        std::size_t posted_index;
        std::optional<IntegerVariableCondition> cond = std::nullopt;
    };

    /**
     * \brief A half-reified edge that canonicalises to `cond -> 0 <= d` with
     * `d < 0`, i.e. to `!cond`.
     *
     * Unconditionally this would be a root contradiction; with a condition it is
     * a fact about that condition instead, and one that *must* be stated --- an
     * implementation that quietly dropped such an edge would allow solutions in
     * which \c cond holds and the edge is violated. The row saturates to the
     * unit clause `~cond`, so the inference is plain RUP against it.
     *
     * \sa DifferenceGraph
     * \ingroup Innards
     */
    struct DifferenceDisallowedCondition
    {
        IntegerVariableCondition cond;
        std::size_t posted_index;
    };

    /**
     * \brief An operand reduced to (bare variable, offset), so that the operand
     * equals `*variable + offset`. A constant operand has no variable, just the
     * offset.
     *
     * \sa deview_difference_operand
     * \ingroup Innards
     */
    struct DeviewedDifferenceOperand
    {
        std::optional<SimpleIntegerVariableID> variable;
        Integer offset;
    };

    /**
     * \brief Reduce an operand to a bare variable plus an offset, or fail on a
     * negated view.
     *
     * Returns `nullopt` for a negated view (`-X + c`): `V - W <= d` with
     * `V = -X + c` is `-X - W <= d - c`, which is not a difference constraint at
     * all --- both coefficients are negative, the graph formulation does not
     * describe it, and treating it as an edge would licence inferences the
     * constraint does not entail. Callers must reject rather than approximate;
     * getting this wrong is unsound, not merely incomplete.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto deview_difference_operand(const IntegerVariableID &) -> std::optional<DeviewedDifferenceOperand>;

    /**
     * \brief A canonicalised system of difference constraints, ready to be
     * propagated: the node list, the edge list over node indices, any static
     * bounds, and one OPB row per contributing constraint.
     *
     * Every operand has been reduced to a bare SimpleIntegerVariableID and the
     * view offsets folded into the weights, so that consecutive edges meeting at
     * "the same variable" really do share a representation and the telescoping
     * `pol` cancels exactly (see `dev_docs/difference-logic.md`).
     *
     * \c edge_lines is indexed by \c posted_index and holds the *already
     * emitted* OPB row stating each edge. It is empty when proofs are off. The
     * propagator only ever cites these rows, never adds any: it derives
     * cutting-planes consequences of constraints the model already contains,
     * which is what lets a presolver build one of these out of other people's
     * constraints after the proof model has been finalised.
     *
     * \ingroup Innards
     */
    struct DifferenceGraph
    {
        std::vector<SimpleIntegerVariableID> nodes;
        std::vector<DifferenceGraphEdge> edges;
        std::vector<DifferenceStaticBound> static_bounds;
        std::vector<DifferenceDisallowedCondition> disallowed_conditions;
        std::vector<ProofLine> edge_lines;
    };

    /**
     * \brief Whether the shared propagator should run the root simplification
     * stage, and where to report what it did.
     *
     * On by default: the paper's section 6.3 measures the simplification stage
     * as most of the difference-logic win (320.95 against 312.94 overall), while
     * the propagator on its own is near-noise. It can be turned off from either
     * entry point so that claim can be checked rather than inherited.
     *
     * \sa install_difference_propagator
     * \ingroup Innards
     */
    struct DifferenceSimplificationOptions
    {
        bool enabled = true;
        std::shared_ptr<DifferenceSimplificationStats> stats = nullptr;
    };

    /**
     * \brief Install the global difference-logic propagator over a canonicalised
     * system, attributed to the given constraint.
     *
     * The propagator runs Bellman-Ford from the current lower bounds over the
     * graph and from the current upper bounds over its reverse, pushing every
     * bound the system implies, and refutes a negative cycle by summing the
     * cycle's rows. It is shared between DifferenceConstraints, which builds the
     * graph from the edges it was posted with, and the difference-logic
     * presolver, which builds it out of donor constraints already posted to the
     * Problem: the algorithm cares only about the node list, the edge list and
     * the rows, never about where they came from.
     *
     * Half-reified edges take part only while their condition currently holds.
     * No inference runs the other way: the propagator never fixes a condition
     * from the graph (the paper's `IncImp`), which its own configuration study
     * says to leave off.
     *
     * A no-op if the system has no edges, static bounds or disallowed
     * conditions. Detecting a root-level contradiction (an *unconditional* edge
     * saying `0 <= d` with `d < 0`) is *not* this function's job --- see
     * DifferenceConstraints::install_propagators, which handles it with an
     * initialiser, a door that has closed by the time a presolver runs. The
     * half-reified counterpart *is* handled here, as a
     * DifferenceDisallowedCondition, precisely because it needs no initialiser.
     *
     * The root simplification stage lives here too, for the same reason: it must
     * infer, and a presolver has no way to. It runs inside the propagator, on its
     * first call, guarded on that call being at the root --- which is where every
     * propagator's first call is, since search starts by propagating everything.
     *
     * \ingroup Innards
     */
    auto install_difference_propagator(Propagators &, const ConstraintID &, DifferenceGraph, DifferenceSimplificationOptions = {}) -> void;
}

#endif
