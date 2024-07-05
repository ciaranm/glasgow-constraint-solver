#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_IN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_IN_HH

#include <gcs/constraint.hh>
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

    public:
        explicit In(IntegerVariableID var, std::vector<IntegerVariableID> vars, std::vector<Integer> vals);
        explicit In(IntegerVariableID var, std::vector<IntegerVariableID> vals);
        explicit In(IntegerVariableID var, std::vector<Integer> vals);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
