#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_PROOF_AUTO_TABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_PROOF_AUTO_TABLE_HH

#include <gcs/presolver.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Create a Table constraint over the specified variables.
     *
     * \ingroup Presolvers
     */
    class ProofAutoTable : public Presolver
    {
    private:
        const std::vector<IntegerVariableID> _vars;

    public:
        explicit ProofAutoTable(const std::vector<IntegerVariableID> & vars);

        virtual auto run(Problem &, innards::Propagators &, innards::State &,
            innards::ProofLogger * const) -> bool override;
        virtual auto clone() const -> std::unique_ptr<Presolver> override;
    };
}

#endif
