#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_GLOBAL_CARDINALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_GLOBAL_CARDINALITY_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/constraints/global_cardinality/bounds_global_cardinality.hh>
#include <gcs/constraints/global_cardinality/gac_global_cardinality.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>
#include <variant>
#include <vector>

namespace gcs
{
    /**
     * \brief The consistency levels supported by GlobalCardinality: bounds
     * consistency (the default, Hall-interval reasoning), or generalised arc
     * consistency (Régin's flow algorithm on the assignment variables; count-GAC
     * is NP-hard, so the count variables stay bounds-consistent either way).
     *
     * \ingroup Consistency
     */
    using GlobalCardinalityConsistency = std::variant<consistency::BC, consistency::GAC>;

    /**
     * \brief Rewrite a cover that repeats a value into one that does not.
     *
     * GlobalCardinality requires its cover values to be pairwise distinct (see
     * below), but a modelling language need not: MiniZinc's `global_cardinality`
     * says only that `counts[i]` is the number of occurrences of `cover[i]`, so
     * a cover of `[1, 1]` is a legal way of saying `counts[0] = counts[1] =` the
     * number of 1s. This turns that into the constraint's own shape.
     *
     * \p values and \p counts are rewritten in place, keeping the first entry
     * for each distinct value and dropping the later ones. Each dropped entry
     * yields a pair `{kept count, dropped count}` in the returned list, and the
     * caller **must** post `Equals` (or an equivalent) over every pair returned,
     * or the dropped count variables are left unconstrained. Self-pairs are not
     * returned, so a cover repeating both a value and its count variable yields
     * nothing to post.
     *
     * This lives here rather than inside the constraint because the `.scp` term
     * is written from the constraint as posted, and cake_pb_cp rebuilds the OPB
     * from that term: a rewrite the constraint did to itself would leave the two
     * encodings describing different things. Doing it in the front end means the
     * `.scp` records the deduplicated cover and the equalities as the separate
     * constraints they are.
     *
     * \throws InvalidProblemDefinitionException if \p values and \p counts have
     * different sizes.
     *
     * \ingroup Constraints
     */
    [[nodiscard]] auto fold_repeated_cover_values(std::vector<Integer> & values, std::vector<IntegerVariableID> & counts)
        -> std::vector<std::pair<IntegerVariableID, IntegerVariableID>>;

    /**
     * \brief The Global Cardinality Constraint: for each `i`, the number of
     * variables in `vars` equal to `values[i]` equals the count variable
     * `counts[i]`. With `.with_closed()`, every variable must take a cover value.
     *
     * Defaults to bounds consistency; request consistency::GAC for Régin flow.
     * The two propagators live as free functions in bounds_global_cardinality.cc
     * and gac_global_cardinality.cc, which this class dispatches between; the
     * choice selects propagation strength only and never changes the OPB
     * encoding (the .scp term does record which propagator ran).
     *
     * The cover values must be **pairwise distinct**, and `values` and `counts`
     * must be the same size; both are checked, and violating either throws. Both
     * propagators assume distinctness -- the bounds arm's Hall reasoning sums the
     * counts over a contiguous slice of the sorted cover, and the GAC arm gives
     * each cover entry its own value node -- so a repeated value used to double
     * the demand for it, losing solutions and emitting an inference VeriPB
     * rejects (issue #922). Call fold_repeated_cover_values() first if the cover
     * comes from somewhere that permits repeats.
     *
     * \ingroup Constraints
     */
    class GlobalCardinality : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        std::vector<Integer> _values;
        std::vector<IntegerVariableID> _counts;
        bool _closed = false;
        GlobalCardinalityConsistency _level = consistency::BC{};

        // Proof lines for each cover value's count constraint
        // Sum_i (x_i == values[j]) == counts[j], stored as {LE-half, GE-half}.
        std::vector<std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>>> _count_lines;

        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

        // The bounds propagator's Hall-interval reasoning ranges over contiguous
        // runs of the cover values, so under consistency::BC they (and their count
        // variables) must be in ascending order. Done in clone() rather than a
        // constructor because the level is chosen post-construction, and both the
        // stored constraint (which s_expr reads) and its install-time clone (which
        // define_proof_model reads) must agree.
        auto sort_cover_values() -> void;

    public:
        /**
         * \throws InvalidProblemDefinitionException if \p values and \p counts
         * have different sizes, or if \p values repeats a value.
         */
        explicit GlobalCardinality(std::vector<IntegerVariableID> vars, std::vector<Integer> values, std::vector<IntegerVariableID> counts);

        /// Select the consistency level: consistency::BC (the default) or
        /// consistency::GAC. Requesting an unsupported level is a compile-time
        /// error, and the choice never changes the OPB encoding.
        auto with_consistency(GlobalCardinalityConsistency level) -> GlobalCardinality &;

        /// Whether the constraint is closed (every variable must take a cover
        /// value). Takes std::optional<bool> so a runtime flag can be passed
        /// straight through; nullopt or no argument closes it.
        auto with_closed(std::optional<bool> closed = true) -> GlobalCardinality &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
