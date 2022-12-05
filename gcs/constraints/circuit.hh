

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CIRCUIT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CIRCUIT_HH


#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Circuit constraint: requires the variables, representing graph nodes, take values
     * such that each variable's value represents the index of the next node in a tour that visits
     * all variables.
     *
     * \ingroup Constraints
     */
    class Circuit : public Constraint {
    private:
        const std::vector<IntegerVariableID> & _succ;
    public:
        explicit Circuit(const std::vector<IntegerVariableID> & vars);

    private:
        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };
}



#endif //GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CIRCUIT_HH