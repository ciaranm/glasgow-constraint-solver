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

        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

        // The bounds propagator's Hall-interval reasoning ranges over contiguous
        // runs of the cover values, so under consistency::BC they (and their count
        // variables) must be in ascending order. Done in clone() rather than a
        // constructor because the level is chosen post-construction, and both the
        // stored constraint (which s_expr reads) and its install-time clone (which
        // define_proof_model reads) must agree.
        auto sort_cover_values() -> void;

    public:
        explicit GlobalCardinality(std::vector<IntegerVariableID> vars, std::vector<Integer> values, std::vector<IntegerVariableID> counts);

        /// Select the consistency level: consistency::BC (the default) or
        /// consistency::GAC. Requesting an unsupported level is a compile-time
        /// error, and the choice never changes the OPB encoding.
        auto with_consistency(GlobalCardinalityConsistency level) -> GlobalCardinality &;

        /// Whether the constraint is closed (every variable must take a cover
        /// value). Takes std::optional<bool> so a runtime flag can be passed
        /// straight through; nullopt or no argument closes it.
        auto with_closed(std::optional<bool> closed = true) -> GlobalCardinality &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
