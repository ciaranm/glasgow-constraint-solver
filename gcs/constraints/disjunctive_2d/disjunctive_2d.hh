#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_2D_DISJUNCTIVE_2D_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_2D_DISJUNCTIVE_2D_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <cstdint>
#include <map>
#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief Disjunctive2D (2D non-overlap, a.k.a. <code>diffn</code>)
     * constraint: rectangles with variable origins; the widths and heights may
     * each be variables or constants (constants pass through as
     * ConstantIntegerVariableID). No two rectangles may overlap in area.
     *
     * Rectangle <em>i</em> occupies <em>[xs[i], xs[i] + widths[i]) &times;
     * [ys[i], ys[i] + heights[i])</em>. Two rectangles do not overlap iff they
     * are separated in at least one direction: <em>xs[i] + widths[i] &le;
     * xs[j]</em>, or <em>xs[j] + widths[j] &le; xs[i]</em>, or <em>ys[i] +
     * heights[i] &le; ys[j]</em>, or <em>ys[j] + heights[j] &le; ys[i]</em>.
     *
     * The <em>strict</em> flag controls zero-area rectangles, mirroring 1D
     * Disjunctive: in strict mode (the default) every rectangle participates
     * (a degenerate rectangle still respects the pairwise separation clause),
     * equivalent to MiniZinc's <code>diffn</code> and XCSP3's
     * <code>zeroIgnored = false</code>; in non-strict mode zero-area rectangles
     * are dropped, equivalent to <code>diffn_nonstrict</code> /
     * <code>zeroIgnored = true</code>.
     *
     * Rectangles may also be <em>optional</em>: the constructor taking a
     * `presences` array makes rectangle <em>i</em> conditional on a {0, 1}
     * variable. A rectangle with <em>presences[i] = 0</em> is absent &mdash; it
     * occupies no area, so it may overlap anything and its origin is
     * unconstrained. The presence appears in the encoding as one more disjunct
     * on each separation clause the rectangle takes part in, and nowhere else,
     * so a rectangle posted with <em>presences[i] = 1</em> and one posted
     * without presences at all produce the same OPB. This is the 1D form's
     * treatment one dimension up: there the 2-way clause becomes 4-way, here
     * the 4-way clause becomes 6-way.
     *
     * Propagation is pairwise 2D time-table strength (the analogue of 1D
     * Disjunctive one dimension up): if two rectangles' mandatory boxes overlap
     * the constraint is infeasible, and if a pair is forced to overlap in one
     * dimension their positions are pushed apart in the other. Stronger
     * reasoning (the cumulative relaxation, a 2D sweep, edge-finding) and
     * k dimensions are left for future work.
     *
     * A rectangle whose presence is still undecided blocks nothing and is
     * pushed nowhere, in either role: a prune that is only valid when the
     * rectangle is there would be wrong if it turns out absent. What it does
     * get is the one inference that needs no such assumption &mdash; if its
     * mandatory box would overlap that of a rectangle known to be present,
     * it cannot be present, and its presence is inferred to be 0.
     *
     * \ingroup Constraints
     */
    class Disjunctive2D : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _xs;
        std::vector<IntegerVariableID> _ys;
        std::vector<IntegerVariableID> _widths;
        std::vector<IntegerVariableID> _heights;
        bool _strict = true;
        std::vector<std::size_t> _active_rects;

        // Per-rectangle presence, as posted; empty for the constructors that
        // take no presences, where every rectangle is unconditionally present.
        // Resolved into _presence by prepare(); this copy exists for clone()
        // and s_expr().
        std::vector<IntegerVariableID> _presences;

        // Per-rectangle presence as resolved by innards::task_presence: nullopt
        // for a rectangle that is unconditionally present --- the non-optional
        // constructors, or a presence argument that is the constant 1 --- which
        // then needs no disjunct in its separation clauses and no presence
        // literal in a reason, so it encodes and propagates exactly as it did
        // before optional rectangles existed. A rectangle whose presence is the
        // constant 0 is dropped from _active_rects and appears nowhere at all.
        // Only *constant* presences resolve: a checker reads the OPB, not the
        // initial State, so a variable whose domain happens to be a singleton
        // keeps its disjunct.
        std::vector<std::optional<IntegerVariableID>> _presence;

        // Size snapshots resolved in prepare(). _*_vals holds the constant
        // value for a constant size (0 for a variable one, where the variable
        // is used instead).
        std::vector<Integer> _width_vals;
        std::vector<Integer> _height_vals;
        // Non-strict mode: whether each rectangle's width/height gets a
        // zero-size escape in the separation clause -- every variable size
        // does, matching cake_pb_cp (std::uint8_t rather than the
        // vector<bool> bitset specialisation).
        std::vector<std::uint8_t> _zero_escape_w, _zero_escape_h;

        // Encoded pairwise reified before-flags, one per (ordered pair, axis).
        // The OPB stays declarative: for each axis d and ordered pair (i, j),
        // before_{i,j,d} <-> pos_{i,d} + size_{i,d} <= pos_{j,d}, plus one 4-way
        // separation clause per unordered pair. Reification line numbers are
        // stored so the propagator's justifications can pol against them.
        struct BeforeFlagData
        {
            innards::ProofFlag flag;
            innards::ProofLine forward_line;
            innards::ProofLine reverse_line;
        };
        // Keyed by (i, j); axis 0 = x, axis 1 = y.
        std::map<std::pair<std::size_t, std::size_t>, BeforeFlagData> _before_x;
        std::map<std::pair<std::size_t, std::size_t>, BeforeFlagData> _before_y;
        std::map<std::pair<std::size_t, std::size_t>, innards::ProofLine> _clause_lines;

        // Non-strict mode only: for a rectangle whose width/height can be 0, a
        // reified "size <= 0" flag that escapes the separation clause (a
        // zero-area rectangle does not constrain). nullopt otherwise.
        std::vector<std::optional<innards::ProofFlag>> _zero_w, _zero_h;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        /**
         * \brief General form: widths and heights may be variables or constants
         * (constants pass through as ConstantIntegerVariableID).
         */
        explicit Disjunctive2D(std::vector<IntegerVariableID> xs, std::vector<IntegerVariableID> ys, std::vector<IntegerVariableID> widths,
            std::vector<IntegerVariableID> heights);

        /**
         * \brief Convenience form for constant rectangle sizes. Delegates to
         * the general constructor.
         */
        explicit Disjunctive2D(
            std::vector<IntegerVariableID> xs, std::vector<IntegerVariableID> ys, std::vector<Integer> widths, std::vector<Integer> heights);

        /**
         * \brief Optional-rectangle form: `presences[i]` is a {0, 1} variable
         * saying whether rectangle `i` is placed at all. An absent rectangle
         * occupies no area and has an unconstrained origin.
         *
         * Each presence must be a variable whose domain is within {0, 1}, or
         * the constant 0 or 1. A constant 1 is the same as leaving the
         * rectangle out of the optional form entirely, and encodes identically.
         *
         * \throws InvalidProblemDefinitionException if a presence's domain is
         * not within {0, 1}, or if the arrays' sizes disagree.
         */
        explicit Disjunctive2D(std::vector<IntegerVariableID> xs, std::vector<IntegerVariableID> ys, std::vector<IntegerVariableID> widths,
            std::vector<IntegerVariableID> heights, std::vector<IntegerVariableID> presences);

        /// Whether the rectangles are strictly disjunctive (zero-area rectangles
        /// also may not overlap); default true. Takes std::optional<bool> so a
        /// runtime flag can be passed straight through.
        auto with_strict(std::optional<bool> strict = true) -> Disjunctive2D &;

        /**
         * \brief The presences this constraint was posted with.
         *
         * Empty for the non-optional constructors, which is how a caller asks
         * "is this an optional-rectangle Disjunctive2D?".
         */
        [[nodiscard]] auto presences() const -> const std::vector<IntegerVariableID> &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
