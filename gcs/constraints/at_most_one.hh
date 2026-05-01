
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_AT_MOST_ONE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_AT_MOST_ONE_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief At most one constraint, at most 1 var can equal val.
     *
     * \ingroup Constraints
     */
    class AtMostOneSmartTable : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        IntegerVariableID _val;
        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;

    public:
        explicit AtMostOneSmartTable(std::vector<IntegerVariableID> vars, IntegerVariableID val);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };

    using AtMostOne = AtMostOneSmartTable;
}

#endif
