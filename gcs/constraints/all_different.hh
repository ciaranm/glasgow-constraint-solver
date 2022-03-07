/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief All different constraint, each var takes a different value.
     *
     * \ingroup Constraints
     * \sa NValue
     */
    class AllDifferent : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> & _vars;

    public:
        explicit AllDifferent(const std::vector<IntegerVariableID> & vars);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };
}

#endif
