#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_NOT_EQUALS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_NOT_EQUALS_HH

#include <gcs/constraint.hh>
#include <gcs/innards/literal.hh>
#include <gcs/variable_id.hh>

#include <string>

namespace gcs
{

    /**
     * \brief Constrain that v1 * v2 = v3, propagated using bounds consistent multiplication.
     *
     * \ingroup Constraints
     */
    class MultBC : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2, _v3;

    public:
        MultBC(IntegerVariableID v1, IntegerVariableID v2, IntegerVariableID v3);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel *) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
