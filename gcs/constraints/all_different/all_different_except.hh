#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_EXCEPT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_EXCEPT_HH

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
     * \brief Constrain that the variables are pairwise distinct, except for
     * any variable taking a value in the excluded set, which is unconstrained
     * by this constraint.
     *
     * Achieves GAC by extending the standard Régin / Tarjan AllDifferent
     * algorithm with a per-variable phantom right-vertex absorbing the
     * "opt-out via an excluded value" choice.
     *
     * \ingroup Constraints
     * \sa AllDifferent
     * \sa AllDifferentExceptZero
     */
    class AllDifferentExcept : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        std::vector<Integer> _excluded;
        std::vector<IntegerVariableID> _sanitised_vars;
        std::vector<Integer> _sanitised_excluded;
        std::vector<Integer> _compressed_vals;
        std::vector<IntegerVariableID> _duplicated_vars;
        bool _has_duplicates = false;
        std::shared_ptr<std::map<Integer, innards::ProofLine>> _value_am1_constraint_numbers;
        std::map<IntegerVariableID, innards::ProofFlag> _duplicate_selectors;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit AllDifferentExcept(std::vector<IntegerVariableID> vars, std::vector<Integer> excluded);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };

    /**
     * \brief Constrain that the variables are pairwise distinct, except for
     * any variable taking the value zero. Equivalent to
     * `AllDifferentExcept{vars, {0_i}}`.
     *
     * \ingroup Constraints
     * \sa AllDifferentExcept
     */
    class AllDifferentExceptZero : public AllDifferentExcept
    {
    public:
        inline explicit AllDifferentExceptZero(std::vector<IntegerVariableID> vars) :
            AllDifferentExcept(std::move(vars), {0_i}) {};
    };
}

#endif
