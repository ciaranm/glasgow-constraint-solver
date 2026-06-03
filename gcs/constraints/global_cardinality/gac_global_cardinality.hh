#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_GAC_GLOBAL_CARDINALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_GAC_GLOBAL_CARDINALITY_HH

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
     * \brief The Global Cardinality Constraint, enforced to generalised arc
     * consistency on the assignment variables via Régin's flow algorithm.
     *
     * Semantics are as for \ref GlobalCardinality: for each `i`, the number of
     * variables in `vars` equal to `values[i]` equals the count variable
     * `counts[i]`; if `closed`, every variable must take a cover value.
     *
     * A value v is removed from a variable x iff no assignment consistent with
     * the current domains and the cardinality bounds has x = v. This is found
     * by a feasible flow in the value graph plus a strongly-connected-component
     * decomposition of its residual. Generalised arc consistency on the count
     * variables is NP-hard, so only the assignment variables reach GAC; the
     * count variables get the achievable occurrence bounds.
     *
     * The `closed` restriction is delegated to an \ref In constraint per
     * variable.
     *
     * \ingroup Constraints
     */
    class GACGlobalCardinality : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        std::vector<Integer> _values;
        std::vector<IntegerVariableID> _counts;
        bool _closed;

        std::vector<std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>>> _count_lines;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit GACGlobalCardinality(std::vector<IntegerVariableID> vars, std::vector<Integer> values,
            std::vector<IntegerVariableID> counts, bool closed = false);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
