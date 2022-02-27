/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    class AllDifferent : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> & _vars;

    public:
        explicit AllDifferent(const std::vector<IntegerVariableID> & vars);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(detail::Propagators &, const detail::State &) && -> void override;
    };
}

#endif
