#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TABLE_TABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TABLE_TABLE_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/extensional_utils.hh>
#include <gcs/extensional.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the specified variables are equal to one of the specified
     * tuples.
     *
     * The constructor takes only the variables and the tuples; select the
     * propagation algorithm with the fluent with_algorithm().
     *
     * \ingroup Constraints
     * \see SmartTable
     */
    class Table : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        ExtensionalTuples _tuples;
        std::shared_ptr<innards::ExtensionalLiveTuples> _live;
        std::shared_ptr<innards::ExtensionalCompactTable> _compact;
        TableAlgorithm _algorithm = table::Auto{};
        bool _has_no_tuples = false;

    public:
        explicit Table(std::vector<IntegerVariableID> vars, ExtensionalTuples tuples);

        /**
         * Select the propagation algorithm: table::Auto by default, or
         * table::LiveSet / table::CompactTable to force one. The choice never
         * changes the constraint's meaning, its search tree, or its proof.
         */
        auto with_algorithm(TableAlgorithm) -> Table &;

        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;
        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;

        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
