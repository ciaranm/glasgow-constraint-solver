#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_SYMMETRIC_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_SYMMETRIC_ALL_DIFFERENT_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <memory>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the variables form an involution: for every
     * index `i` in `[start, start + size)`, `x[i]` lies in
     * `[start, start + size)`, the variables are pairwise distinct, and
     * `x[x[i] - start] = i + start`.
     *
     * Achieves AllDifferent-GAC plus Régin's pairwise channeling rule
     * on the inverse. This is strictly weaker than the
     * symmetric-alldifferent GAC of Régin (1999) — the latter requires
     * non-bipartite matching and is left as future work.
     *
     * \ingroup Constraints
     * \sa AllDifferent
     * \sa Inverse
     */
    class SymmetricAllDifferent : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        Integer _start;
        std::shared_ptr<std::map<Integer, innards::ProofLine>> _value_am1s;
        bool _has_duplicate_vars = false;
        std::map<IntegerVariableID, innards::ProofFlag> _duplicate_selectors;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit SymmetricAllDifferent(std::vector<IntegerVariableID> vars, Integer start = 0_i);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name,
            const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
