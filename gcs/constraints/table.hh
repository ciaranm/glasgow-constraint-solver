#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TABLE_HH

#include <gcs/constraint.hh>
#include <gcs/extensional.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the specified variables are equal to one of the specified
     * tuples.
     *
     * \ingroup Constraints
     * \see SmartTable
     */
    class Table : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        ExtensionalTuples _tuples;

    public:
        explicit Table(std::vector<IntegerVariableID> vars, ExtensionalTuples tuples);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

    /**
     * \brief Constrain that the specified variables are not equal to one of the specified
     * tuples.
     *
     * \ingroup Constraints
     */
    class NegativeTable : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        ExtensionalTuples _tuples;

    public:
        explicit NegativeTable(std::vector<IntegerVariableID> vars, ExtensionalTuples tuples);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
