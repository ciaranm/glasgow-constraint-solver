/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TABLE_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the specified variables are equal to one of the specified
     * tuples.
     *
     * \ingroup Constraints
     */
    class Table : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> & _vars;
        std::vector<std::vector<Integer>> && _tuples;

    public:
        explicit Table(const std::vector<IntegerVariableID> & vars, std::vector<std::vector<Integer>> && tuples);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };
}

#endif
