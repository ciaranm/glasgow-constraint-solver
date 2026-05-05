#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COUNT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COUNT_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/variable_id.hh>

#include <tuple>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the value of interest appears exactly how many times in
     * the array.
     *
     * \ingroup Constraints
     */
    class Count : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        IntegerVariableID _value_of_interest, _how_many;
        std::vector<std::tuple<innards::ProofFlag, innards::ProofFlag, innards::ProofFlag>> _flags;

        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Count(std::vector<IntegerVariableID>, const IntegerVariableID & value_of_interest, const IntegerVariableID & how_many);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
