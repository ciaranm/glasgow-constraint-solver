
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Lexicographic ordering constraint. Enforce vars_1 >_lex vars_2.
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

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

    // Currently only implemented via a Smart Table
    using Lex = LexSmartTable;
}

#endif
