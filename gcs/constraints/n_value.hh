#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_N_VALUE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_N_VALUE_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <list>
#include <map>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that a variable is equal to the number of distinct
     * values among the array of variables.
     *
     * \ingroup Constraints
     * \sa AllDifferent
     */
    class NValue : public Constraint
    {
    private:
        IntegerVariableID _n_values;
        const std::vector<IntegerVariableID> _vars;
        std::map<Integer, std::list<IntegerVariableID>> _possible_values;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit NValue(const IntegerVariableID &, std::vector<IntegerVariableID>);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
