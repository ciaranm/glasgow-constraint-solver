#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_2D_DISJUNCTIVE_2D_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_2D_DISJUNCTIVE_2D_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/constraints/innards/disjunctive_2d_mutations.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

namespace gcs::innards
{
    struct CumulativeInputs;
}

namespace gcs
{
    /**
     * \brief Which of Disjunctive2D's propagation rules are enabled.
     *
     * Turning one off weakens propagation but never changes the solutions
     * found, and never changes the OPB encoding: these select propagation
     * strength only, so that a test can attribute an inference to the rule that
     * made it, and so that a fixture can show a rule is load-bearing by
     * watching a solve without it fail to make the inference. Same intent as
     * DisjunctiveRules one dimension down.
     *
     * The pairwise 2D time-table is not among them and is always on: it is
     * what checks a fully assigned pair, so a solve without it would report
     * overlapping rectangles as solutions rather than merely propagate less.
     *
     * \ingroup Constraints
     */
    struct Disjunctive2DRules
    {
        /**
         * \brief The cumulative relaxation: project onto one axis and
         * time-table the `Cumulative` that projection implies, on each axis in
         * turn.
         *
         * Project onto x and rectangle `i` becomes a task with start `x_i`,
         * duration `w_i` and *height* `h_i`, on a resource whose capacity is
         * the y extent the rectangles are confined to. That is a real
         * `Cumulative`, and it sees conflicts the pairwise rule cannot: three
         * rectangles whose mandatory x parts share a time, no two of whose
         * mandatory boxes overlap, can still be too tall between them to fit in
         * the y window.
         *
         * Nothing reaches the OPB --- the relaxation is a consequence of the
         * 4-way separation clause, so it is *derived*, per firing, inside the
         * proof. Two rectangles that both occupy a time on the time axis can
         * satisfy neither of that clause's time-axis disjuncts, so what is left
         * of the clause separates them on the resource axis; the set occupying
         * that time is then pairwise separated, and
         * innards::ComparatorNetwork sorts it and telescopes to "the window is
         * at least as tall as what is in it", which the firing says it is not.
         * See #972, and dev_docs/disjunctive-proof-logging.md.
         *
         * Off by default, and the cost is in two places. The *sweep* is cubic
         * in the number of rectangles per propagator call --- for each one, a
         * blocked time is looked for over the load profile's segments, and each
         * segment costs a pass over the others --- and a solve that never fires
         * the rule pays it anyway: measured at 1.74x wall clock, with proofs
         * off, on an instance where it prunes 0.4%. The *certificate* is then a
         * comparator network per firing, `O(|S|^3)` in the size of the set.
         *
         * Against that, where it does fire it can be the whole solve: on
         * `examples/squares`, five squares of three in a box five wide goes
         * from 156,856 search nodes to one, and its proof from 145 MB to
         * 218 KB. Both arms verify. What it buys on a corpus rather than on a
         * packing family has not been measured.
         *
         * A rectangle takes part on an axis only if its size *on the other*
         * axis is a positive constant, its position there is a plain variable
         * with a non-negative domain, and that domain is narrow enough for the
         * network's guard coefficients --- the conditions
         * innards::ComparatorNetwork::wire_over imposes. Those are all
         * properties of the model rather than of the search state, so they are
         * settled once, in `prepare()`, and the same set is used whether or not
         * proofs are on: a rectangle the certificate could not speak about
         * takes no part in the *inference* either, rather than the two drifting
         * apart.
         */
        bool cumulative_relaxation = false;

        /**
         * \brief The overload check on each axis's cumulative relaxation:
         * rectangles lying wholly inside a time-axis window `[a, b)` whose
         * total area exceeds `H * (b - a)` cannot all be there, `H` being the
         * resource-axis extent the model confines them to.
         *
         * This is the first *energetic* rung over the relaxation, and it is
         * one \ref cumulative_relaxation's certificate cannot reach: that one
         * speaks about the rectangles whose mandatory parts cover a time,
         * where this one sums a capacity row over every rectangle that *may*
         * be active at each time in the window. So the row is the flagged one,
         * `sum_i h_i * active_{i,t} <= H`, and it is derived once per time
         * point, at `ProofLevel::Top`, by an innards::ComparatorNetwork over
         * optional tasks (ComparatorNetwork::add_optional_task): an inactive
         * rectangle is a zero-height dummy parked at the top of the window.
         * The activity flags are minted by redundance over the time-axis
         * order literals, as 1D Disjunctive's time-indexed overload
         * certificate does, and the per-rectangle window energies are the
         * same telescope. See #984.
         *
         * Uses the members \ref cumulative_relaxation does, restricted to a
         * constant time-axis size, and `H` is the model's resource-axis
         * extent over them rather than the current one, since the row is
         * cached. The network's constants are quadratic in that extent, so an
         * axis whose members' resource-axis window does not pass
         * innards::ComparatorNetwork::fits_optional_tasks --- from zero, one
         * ending at 2^31 or later --- runs none of the rules citing the row,
         * whether or not proofs are on. Off by default; independent of \ref
         * cumulative_relaxation.
         */
        bool relaxation_overload = false;

        /**
         * \brief Edge-finding on each axis's cumulative relaxation: a
         * rectangle with exactly one time-axis end inside a window `[a, b)`,
         * which the rectangles the window contains leave too little room for,
         * is pushed away from it --- `Cumulative`'s edge-finding with the
         * capacity `H` of \ref relaxation_overload.
         *
         * The certificate is that rule's, emitted under the negated
         * conclusion: the same flagged row per time point, plus each
         * rectangle's guarded window energy (the row 1D Disjunctive's
         * edge-finding cites, `window_energy::derive_guarded_window_energy`)
         * times its height, with the pushed rectangle's conclusion guard left
         * standing so the sum derives the push. Constant sizes, as for \ref
         * relaxation_overload. Off by default.
         */
        bool relaxation_edge_finding = false;

        /**
         * \brief Time-table edge-finding on each axis's cumulative
         * relaxation: \ref relaxation_edge_finding with the mandatory-part
         * load of the rectangles a window does not contain counted too, as
         * `Cumulative`'s TTEF counts its profile.
         *
         * The certificate is edge-finding's plus one pin per profile
         * rectangle and time point, `active_{i,t} >= 1` under the reason's
         * bounds on it, times its height. Subsumes \ref
         * relaxation_edge_finding. Off by default.
         */
        bool relaxation_time_table_edge_finding = false;

        /**
         * \brief Run `Cumulative`'s own propagator, with these rules, on each
         * axis's projection: the whole certified cumulative ladder rather
         * than the rungs above one at a time.
         *
         * Project onto an axis and each rectangle is a task with that axis's
         * position and size as its start and length and the other axis's size
         * as its height, on a resource of capacity `H`, the model's extent on
         * the other axis. A `Cumulative` states that with per-(task, time)
         * activity flags and one capacity row per time point in its OPB;
         * this constraint has neither, so it supplies both inside the proof
         * (#973). The flags are *named* with the model, under
         * `ConstraintProofModelData<Cumulative>`'s keys at position `axis x n
         * + i`, and *defined* by `red`, on demand, exactly as a
         * start-checkpoint `Cumulative` defines its own. The row at a time
         * point is \ref relaxation_overload's flagged row, over those flags,
         * derived by innards::ComparatorNetwork the first time something
         * cites it and cached at `ProofLevel::Top`. Past that the propagator
         * and every certificate it writes are `Cumulative`'s, unchanged.
         *
         * Uses the members \ref relaxation_overload does, and is off on an
         * axis where that rule is for the width of its window. nullopt, the
         * default, runs nothing.
         */
        std::optional<CumulativeRules> cumulative_projection = std::nullopt;
    };

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
     * dimension their positions are pushed apart in the other. On top of that,
     * and off by default, the *cumulative relaxation* time-tables the
     * `Cumulative` each axis projection implies --- see
     * Disjunctive2DRules::cumulative_relaxation --- and, also off by default,
     * checks it for overload, edge-finding and TTEF
     * (Disjunctive2DRules::relaxation_overload and the two after it), or runs
     * `Cumulative`'s own propagator on each projection with whichever of its
     * rules are asked for (Disjunctive2DRules::cumulative_projection). A 2D
     * sweep and k dimensions are left for future work; see #976.
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
            /// The big-M the reifier chose for the forward row, asked for
            /// rather than assumed: the cumulative relaxation's comparator
            /// network raises that row to its own guard coefficient, and the
            /// two directions of a pair get different constants whenever their
            /// sizes or encoding widths differ.
            Integer forward_guard_coefficient;
        };
        // Keyed by (i, j); axis 0 = x, axis 1 = y.
        std::map<std::pair<std::size_t, std::size_t>, BeforeFlagData> _before_x;
        std::map<std::pair<std::size_t, std::size_t>, BeforeFlagData> _before_y;
        std::map<std::pair<std::size_t, std::size_t>, innards::ProofLine> _clause_lines;

        // Non-strict mode only: for a rectangle whose width/height can be 0, a
        // reified "size <= 0" flag that escapes the separation clause (a
        // zero-area rectangle does not constrain). nullopt otherwise.
        std::vector<std::optional<innards::ProofFlag>> _zero_w, _zero_h;

        Disjunctive2DRules _rules;
        innards::Disjunctive2DProofMutation _mutation;

        // Which rectangles the cumulative relaxation may use, by which axis
        // plays the part of time: index 0 is x as time (so the set at a time
        // point is sorted on y), index 1 is y as time. Resolved in prepare(),
        // from the model alone, so that the rule makes the same inferences
        // whether or not proofs are on.
        std::array<std::vector<std::size_t>, 2> _relaxation_members;

        // For the relaxation's overload check: per axis, the resource-axis
        // window the model confines the members to, and each member's declared
        // time-axis position bounds. Both are model facts, which is what lets
        // the capacity row the check cites be cached at Top.
        std::array<std::pair<Integer, Integer>, 2> _relaxation_window{{{Integer{0}, Integer{0}}, {Integer{0}, Integer{0}}}};
        std::array<std::map<std::size_t, std::pair<Integer, Integer>>, 2> _relaxation_declared_time;

        // Per axis, whether that window is narrow enough for the flagged
        // capacity row's network, whose optional tasks have constants
        // quadratic in it (innards::ComparatorNetwork::fits_optional_tasks).
        // Where it is not, the rules citing the row --- the energetic rungs
        // and the projection --- are off on that axis, proofs or not.
        std::array<bool, 2> _relaxation_row_fits{{false, false}};

        // Disjunctive2DRules::cumulative_projection, per axis: the rectangles
        // projected, in the order the projected Cumulative numbers its tasks,
        // and that Cumulative's inputs, built by prepare() and given their
        // flags by define_proof_model(). Null where the axis projects nothing.
        std::array<std::vector<std::size_t>, 2> _projection_rects;
        std::array<std::shared_ptr<innards::CumulativeInputs>, 2> _projection;

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

        /// Select which propagation rules run; see Disjunctive2DRules.
        auto with_rules(Disjunctive2DRules rules) -> Disjunctive2D &;

        /// Corrupt the cumulative relaxation's certificate. For tests only,
        /// which assert that VeriPB rejects the result; see
        /// innards::Disjunctive2DProofMutation.
        auto with_proof_mutation(innards::Disjunctive2DProofMutation mutation) -> Disjunctive2D &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
