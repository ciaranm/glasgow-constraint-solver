#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_CONSTRAINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIFFERENCE_DIFFERENCE_CONSTRAINTS_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/difference/difference_graph.hh>
#include <gcs/integer.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace gcs
{
    /**
     * \brief One edge of a DifferenceConstraints system: \f$x - y \le d\f$, or
     * \f$cond \rightarrow x - y \le d\f$ when \c cond is given.
     *
     * Either operand may be a view or a constant. A negated view (`-X + c`) is
     * rejected: `V - W <= d` with `V = -X + c` is `-X - W <= d - c`, which is
     * not a difference constraint at all.
     *
     * A \c cond makes the edge *half-reified*: the constraint holds only when
     * the condition does, and the edge takes part in the graph only while the
     * condition currently holds. Nothing is inferred in the other direction ---
     * the condition is never fixed from the graph. That is the paper's
     * `IncImp`, which its own configuration study says to leave off, so it is
     * deliberately absent; posting `b -> x - y <= d` on its own therefore leaves
     * `b` for the search (or for some other constraint) to decide.
     *
     * \sa DifferenceConstraints
     * \ingroup Constraints
     */
    struct DifferenceEdge
    {
        IntegerVariableID x;
        IntegerVariableID y;
        Integer d;
        std::optional<IntegerVariableCondition> cond = std::nullopt;
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
     * An edge may carry a reification condition, giving `b -> x - y <= d`; such
     * an edge participates only while its condition currently holds, and every
     * inference made using it cites that condition. Inference in the other
     * direction (fixing a condition because its edge would close a negative
     * cycle --- the paper's `IncImp`) is deliberately not implemented, since the
     * paper's own configuration study says to leave it off. Note also the
     * paper's caveat in its section 4.1: its "this is a domain propagator"
     * claim assumes no Boolean appears in two difference constraints, which a
     * disjunctive encoding (`b -> i before j`, `!b -> j before i`) violates by
     * construction. That is a *completeness* caveat only; soundness is
     * unaffected, and this propagator is bounds consistent rather than domain
     * consistent in any case.
     *
     * Incremental propagation is not implemented: every wake recomputes from
     * scratch.
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

        // The canonical graph, built by prepare() and filled in with one
        // labelled OPB row per posted edge by define_proof_model(). Every
        // operand is reduced to a bare SimpleIntegerVariableID plus an offset,
        // and the offsets are folded into the weight, so that every edge's OPB
        // row speaks the same representation and the telescoping pol cancels
        // exactly. The propagator itself is shared with the difference-logic
        // presolver, which builds one of these out of constraints somebody else
        // posted; see innards::install_difference_propagator.
        innards::DifferenceGraph _graph;

        // An edge whose two operands canonicalise to the same thing (aliasing,
        // or two constants) says 0 <= d. Harmless when d >= 0; a root
        // contradiction when d < 0, in which case its OPB row is directly
        // false, so the contradiction RUPs from the model with nothing cited.
        // Only whether this is engaged is acted on; the index identifies the
        // first offending edge, for a future assertion hint to name.
        std::optional<std::size_t> _root_contradiction_posted_index;

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
