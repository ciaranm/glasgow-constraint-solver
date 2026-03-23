#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH 1

#include <gcs/constraint.hh>
#include <gcs/expression.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/reification.hh>

#include <memory>

namespace gcs
{
    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is less than or equal to the specified
     * value, if and possibly only if the condition holds.
     *
     * \ingroup innards
     * \sa LinearLessThanEqual
     * \sa LinearGreaterThanEqual
     */
    class ReifiedLinearInequality : public Constraint
    {
    private:
        WeightedSum _coeff_vars;
        Integer _value;
        ReificationCondition _reif_cond;

    public:
        explicit ReifiedLinearInequality(WeightedSum coeff_vars, Integer value, ReificationCondition cond);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
