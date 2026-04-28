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
        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;

    public:
        explicit Table(std::vector<IntegerVariableID> vars, ExtensionalTuples tuples);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;

        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
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
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;
        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;

    public:
        explicit NegativeTable(std::vector<IntegerVariableID> vars, ExtensionalTuples tuples);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
