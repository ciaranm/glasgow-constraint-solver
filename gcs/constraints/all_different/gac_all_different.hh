#ifndef GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH
#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief GAC all different constraint, each var takes a different value, and do GAC pruning.
     *
     * \ingroup Constraints
     * \sa NValue
     */
    class GACAllDifferent : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;

    public:
        explicit GACAllDifferent(std::vector<IntegerVariableID> vars);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

}
#endif // GLASGOW_CONSTRAINT_SOLVER_GAC_ALL_DIFFERENT_HH
