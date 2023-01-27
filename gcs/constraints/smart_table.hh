#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_TABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_TABLE_HH

#include <gcs/constraint.hh>
#include <gcs/extensional.hh>
#include <gcs/smart_entry.hh>
#include <gcs/variable_id.hh>

namespace gcs
{
    class SmartTable : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        SmartTuples _tuples;

    public:
        explicit SmartTable(std::vector<IntegerVariableID> vars, SmartTuples tuples);
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_SMART_TABLE_HH
