#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_IN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_IN_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that `var` is equal to one of the specified values, or to
     * one of the specified variables.
     *
     * The value list and variable list are unioned: the constraint is satisfied
     * iff `var` equals at least one constant in the value list, or equals at
     * least one variable in the variable list.
     *
     * \ingroup Constraints
     */
    class In : public Constraint
    {
    private:
        IntegerVariableID _var;
        std::vector<IntegerVariableID> _var_vals;
        std::vector<Integer> _val_vals;
        std::vector<innards::ProofFlag> _selectors;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit In(IntegerVariableID var, std::vector<IntegerVariableID> vars, std::vector<Integer> vals);
        explicit In(IntegerVariableID var, std::vector<IntegerVariableID> vals);
        explicit In(IntegerVariableID var, std::vector<Integer> vals);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
