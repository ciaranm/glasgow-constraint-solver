#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_GRAPH_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_GRAPH_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <optional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief One edge of a canonicalised difference system: `nodes[from] -
     * nodes[to] <= d`, derived from the `posted_index`th constraint the caller
     * handed over.
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
    };

    /**
     * \brief An edge with a constant operand, which is not a graph edge at all
     * but a plain bound on the other operand: `nodes[node] >= value` when
     * `is_lower`, `nodes[node] <= value` otherwise.
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
        std::vector<ProofLine> edge_lines;
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
     * A no-op if the system has neither edges nor static bounds. Detecting a
     * root-level contradiction (an edge saying `0 <= d` with `d < 0`) is *not*
     * this function's job --- see DifferenceConstraints::install_propagators,
     * which handles it with an initialiser, a door that has closed by the time a
     * presolver runs.
     *
     * \ingroup Innards
     */
    auto install_difference_propagator(Propagators &, const ConstraintID &, DifferenceGraph) -> void;
}

#endif
