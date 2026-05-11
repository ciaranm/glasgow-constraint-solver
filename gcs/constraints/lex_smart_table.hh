
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LEX_SMART_TABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LEX_SMART_TABLE_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Lexicographic ordering constraint, encoded as a SmartTable.
     * Enforce vars_1 >_lex vars_2.
     *
     * Kept around for benchmarking and as a reference encoding; for
     * normal use, prefer LexGreaterThan (or one of the other dedicated
     * Lex* constraints in lex.hh), which share a single specialised
     * propagator and produce smaller, cleaner proofs.
     *
     * \ingroup Constraints
     */
    class LexSmartTable : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars_1;
        std::vector<IntegerVariableID> _vars_2;

    public:
        explicit LexSmartTable(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
