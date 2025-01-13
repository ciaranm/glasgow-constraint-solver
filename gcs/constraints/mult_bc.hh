#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULT_BC_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULT_BC_HH

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
        SimpleIntegerVariableID _v1, _v2, _v3;

    public:
        MultBC(SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3);

        virtual auto install(innards::Propagators & propagators, innards::State &, innards::ProofModel *) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
