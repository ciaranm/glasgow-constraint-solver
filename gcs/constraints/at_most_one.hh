
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ABS_HH

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

    public:
        explicit AtMostOneSmartTable(std::vector<IntegerVariableID> vars, IntegerVariableID val);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

    using AtMostOne = AtMostOneSmartTable;
}

#endif
