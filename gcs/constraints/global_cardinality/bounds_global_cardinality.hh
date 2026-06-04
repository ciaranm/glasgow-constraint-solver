#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_BOUNDS_GLOBAL_CARDINALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_BOUNDS_GLOBAL_CARDINALITY_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief The Global Cardinality Constraint, enforced to bounds consistency
     * via Hall-interval reasoning over the cover values.
     *
     * Semantics are as for \ref GlobalCardinality: for each `i`, the number of
     * variables in `vars` equal to `values[i]` equals the count variable
     * `counts[i]`; if `closed`, every variable must take a cover value.
     *
     * This is a single dedicated propagator. It tightens the count variables
     * from the must-occur/can-occur counts and
     * prunes the assignment variables using generalised Hall sets: an interval
     * of cover values whose total upper capacity is saturated by the variables
     * confined to it forbids those values elsewhere, and an interval whose total
     * lower demand exactly matches the variables able to supply it forces those
     * variables into it. Generalised arc consistency on the count variables is
     * NP-hard, so only bounds consistency is enforced there.
     *
     * The `closed` restriction is delegated to an \ref In constraint per
     * variable.
     *
     * \ingroup Constraints
     */
    class BoundsGlobalCardinality : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        std::vector<Integer> _values;
        std::vector<IntegerVariableID> _counts;
        bool _closed;

        // Proof lines for each cover value's count constraint
        // Sum_i (x_i == values[j]) == counts[j], stored as {LE-half, GE-half}.
        std::vector<std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>>> _count_lines;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit BoundsGlobalCardinality(std::vector<IntegerVariableID> vars, std::vector<Integer> values,
            std::vector<IntegerVariableID> counts, bool closed = false);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
