#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_CONSTRAINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_CONSTRAINTS_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace gcs
{
    /**
     * \brief One edge of a DifferenceConstraints system: \f$x - y \le d\f$.
     *
     * Either operand may be a view or a constant. A negated view (`-X + c`) is
     * rejected: `V - W <= d` with `V = -X + c` is `-X - W <= d - c`, which is
     * not a difference constraint at all.
     *
     * \sa DifferenceConstraints
     * \ingroup Constraints
     */
    struct DifferenceEdge
    {
        IntegerVariableID x;
        IntegerVariableID y;
        Integer d;
    };

    /**
     * \brief Constrain that \f$x - y \le d\f$ for every edge in a set of
     * difference constraints, propagated globally rather than one edge at a
     * time.
     *
     * The system is a weighted digraph with a vertex per variable and an edge
     * \f$x \xrightarrow{d} y\f$ per constraint. The system is satisfiable iff
     * that graph has no negative-weight cycle, and it entails
     * \f$x - y \le d\f$ exactly when the shortest path from \c x to \c y weighs
     * at most \c d (Dechter, Meiri and Pearl; see Kletzander, Dekker, Schutt and
     * Stuckey, "Global Difference Constraint Propagation for Constraint
     * Programming", arXiv:2607.20022, Theorem 1). Posting the same system as
     * individual two-term LinearLessThanEqual constraints gives the same
     * solutions, but reaching the bounds fixpoint can take asymptotically more
     * work, because bounds crawl along the graph one propagator wake at a time
     * (the paper's Example 8, measured in `examples/difference_chain`).
     *
     * This propagator is bounds consistent for the system as a whole: it runs
     * Bellman-Ford from the current lower bounds over the graph and from the
     * current upper bounds over its reverse, and pushes every bound the system
     * implies in one pass. It reads and writes bounds only, so it never removes
     * an interior value, and gcs domains may have holes where the paper's
     * Theorem 2 assumes ranges.
     *
     * This version handles unconditional edges only. Half-reified edges
     * (`b -> x - y <= d`), which make the graph change during search, are not
     * supported yet. Neither is incremental propagation: every wake recomputes
     * from scratch.
     *
     * See `dev_docs/difference-logic.md` for the design, the proof shapes and
     * what is deferred.
     *
     * \ingroup Constraints
     */
    class DifferenceConstraints : public Constraint
    {
    private:
        // The edges exactly as posted. Kept for s_expr() and clone(); the
        // propagator works off the canonical form below.
        std::vector<DifferenceEdge> _edges;

        // The canonical graph, built by prepare(). Every operand is reduced to
        // a bare SimpleIntegerVariableID plus an offset, and the offsets are
        // folded into the weight, so that every edge's OPB row speaks the same
        // representation and the telescoping pol cancels exactly.
        std::vector<SimpleIntegerVariableID> _nodes;

        struct GraphEdge
        {
            std::size_t from;
            std::size_t to;
            Integer d;
            std::size_t posted_index;
        };

        // A constant operand does not give a graph edge, it gives a static
        // bound on the other operand.
        struct StaticBound
        {
            std::size_t node;
            Integer value;
            bool is_lower;
            std::size_t posted_index;
        };

        std::vector<GraphEdge> _graph_edges;
        std::vector<StaticBound> _static_bounds;

        // An edge whose two operands canonicalise to the same thing (aliasing,
        // or two constants) says 0 <= d. Harmless when d >= 0; a root
        // contradiction when d < 0, in which case its OPB row is directly
        // false, so the contradiction RUPs from the model with nothing cited.
        // Only whether this is engaged is acted on; the index identifies the
        // first offending edge, for a future assertion hint to name.
        std::optional<std::size_t> _root_contradiction_posted_index;

        // One labelled OPB row per posted edge, indexed by posted position.
        // Empty when proofs are off.
        std::vector<innards::ProofLine> _edge_lines;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit DifferenceConstraints(std::vector<DifferenceEdge> edges);

        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
