#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_NOT_EQUALS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_NOT_EQUALS_HH

#include <gcs/constraint.hh>
#include <gcs/innards/literal.hh>
#include <gcs/variable_id.hh>

#include <string>

namespace gcs
{

    /**
     * \brief Constrain that two variables are not equal.
     *
     * \ingroup Constraints
     */
    class NotEquals : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;

    public:
        NotEquals(const IntegerVariableID v1, const IntegerVariableID v2);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
