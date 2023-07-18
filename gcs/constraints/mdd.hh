

#ifndef GLASGOW_CONSTRAINT_SOLVER_MDD_HH
#define GLASGOW_CONSTRAINT_SOLVER_MDD_HH

class mdd
{
};

#endif // GLASGOW_CONSTRAINT_SOLVER_MDD_HH
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MDD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MDD_HH

#include <gcs/constraint.hh>
#include <gcs/extensional.hh>
#include <gcs/variable_id.hh>
#include <unordered_map>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the sequence of variables is a member of the
     * language recognised by the given multivalued decision diagram (MDD).
     *
     * \ingroup Constraints
     */
    class MDD : public Constraint
    {
    private:


    public:
        explicit MDD();

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
