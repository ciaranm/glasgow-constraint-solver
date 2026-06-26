#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_2D_DISJUNCTIVE_2D_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_2D_DISJUNCTIVE_2D_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_only_variables-fwd.hh>
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
     * Propagation is pairwise 2D time-table strength (the analogue of 1D
     * Disjunctive one dimension up): if two rectangles' mandatory boxes overlap
     * the constraint is infeasible, and if a pair is forced to overlap in one
     * dimension their positions are pushed apart in the other. Stronger
     * reasoning (the cumulative relaxation, a 2D sweep, edge-finding) and
     * k dimensions are left for future work.
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
        bool _strict;
        std::vector<std::size_t> _active_rects;

        // Size snapshots resolved in prepare(). _*_vals holds the constant
        // value for a constant size (0 for a variable one, where the variable
        // is used instead); _*_ub holds the initial upper bound (used for the
        // possible-active window and the active-rect filter).
        std::vector<Integer> _width_vals, _width_ub;
        std::vector<Integer> _height_vals, _height_ub;
        // Non-strict mode: whether each rectangle's width/height can be 0
        // (std::uint8_t rather than the vector<bool> bitset specialisation).
        std::vector<std::uint8_t> _can_be_zero_w, _can_be_zero_h;

        // Per-rectangle possible-active windows in each dimension, from root
        // bounds in prepare(). Used to size the proof bridge and to index the
        // per-(rect, coordinate) bridge flags. Only meaningful for positive-size
        // rectangles in the relevant dimension.
        std::vector<Integer> _x_lo, _x_hi;
        std::vector<Integer> _y_lo, _y_hi;

        // Encoded pairwise reified before-flags, one per (ordered pair, axis).
        // The OPB stays declarative: for each axis d and ordered pair (i, j),
        // before_{i,j,d} <-> pos_{i,d} + size_{i,d} <= pos_{j,d}, plus one 4-way
        // separation clause per unordered pair. Reification line numbers are
        // stored so the propagator's bridge derivations can pol them.
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

        // For a rectangle with a variable size on an axis, a proof-only
        // end = pos + size on which that axis's "after" bridge flag is reified
        // (single variable, keeping the after pin RUP-friendly). Both definition
        // lines are captured: _end_*_ge is end >= pos+size (used to materialise
        // end's bound), _end_*_le is end <= pos+size (used to cancel end back to
        // pos+size in the before-flag pol). nullopt when that size is constant.
        std::vector<std::optional<innards::ProofOnlySimpleIntegerVariableID>> _end_x, _end_y;
        std::vector<std::optional<innards::ProofLine>> _end_x_ge, _end_x_le, _end_y_ge, _end_y_le;

        // Non-strict mode only: for a rectangle whose width/height can be 0, a
        // reified "size <= 0" flag that escapes the separation clause (a
        // zero-area rectangle does not constrain). nullopt otherwise.
        std::vector<std::optional<innards::ProofFlag>> _zero_w, _zero_h;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        /**
         * \brief General form: widths and heights may be variables or constants
         * (constants pass through as ConstantIntegerVariableID).
         */
        explicit Disjunctive2D(std::vector<IntegerVariableID> xs, std::vector<IntegerVariableID> ys, std::vector<IntegerVariableID> widths,
            std::vector<IntegerVariableID> heights, bool strict = true);

        /**
         * \brief Convenience form for constant rectangle sizes. Delegates to
         * the general constructor.
         */
        explicit Disjunctive2D(std::vector<IntegerVariableID> xs, std::vector<IntegerVariableID> ys, std::vector<Integer> widths,
            std::vector<Integer> heights, bool strict = true);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
    };
}

#endif
