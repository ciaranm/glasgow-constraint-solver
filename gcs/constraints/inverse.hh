#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INVERSE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INVERSE_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <memory>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that `x[i] = j <-> y[j] = i`. By default the arrays
     * are zero-indexed, but the x_start and y_start arguments can be used
     * to specify a different starting index.
     *
     * \ingroup Constraints
     */
    class Inverse : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _x, _y;
        const Integer _x_start, _y_start;
        std::shared_ptr<std::map<Integer, innards::ProofLine>> _x_value_am1s;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Inverse(std::vector<IntegerVariableID> x, std::vector<IntegerVariableID> y,
            Integer x_start = 0_i, Integer y_start = 0_i);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
