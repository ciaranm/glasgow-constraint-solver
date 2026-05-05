#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_AMONG_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_AMONG_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain the number of times that a set of constant values appear
     * in an array of variables.
     *
     * \ingroup Constraints
     */
    class Among : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        const std::vector<Integer> _values_of_interest;
        IntegerVariableID _how_many;
        std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>> _sum_line;

        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Among(std::vector<IntegerVariableID>, const std::vector<Integer> & values_of_interest, const IntegerVariableID & how_many);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
