/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

namespace gcs
{
    /**
     * \brief Absolute value constraint, `v2 = abs(v1)`.
     *
     * \ingroup Constraints
     */
    class Abs : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;

    public:
        explicit Abs(const IntegerVariableID v1, const IntegerVariableID v2);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };
}

#endif
