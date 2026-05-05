#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_IN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_IN_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/table.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that `var in vals`.
     *
     * \ingroup Constraints
     */
    class In : public Constraint
    {
    private:
        IntegerVariableID _var;
        std::vector<IntegerVariableID> _var_vals;
        std::vector<Integer> _val_vals;
        std::unique_ptr<Table> _table;
        
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;
        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;

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
