#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH 1

#include <gcs/constraint.hh>
#include <gcs/expression.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>

#include <memory>

namespace gcs
{
    namespace innards
    {
        /**
         * \brief Constrain that the sum of the variables multiplied by their
         * associated coefficients is less than or equal to the specified
         * value, if and only if the condition holds.
         *
         * \ingroup innards
         * \sa LinearLessEqual
         * \sa LinearGreaterThanEqual
         */
        class LinearInequalityIff : public Constraint
        {
        private:
            WeightedSum _coeff_vars;
            Integer _value;
            Literal _cond;

        public:
            explicit LinearInequalityIff(WeightedSum coeff_vars, Integer value, Literal cond);

            virtual auto install(innards::Propagators &, innards::State &,
                innards::ProofModel * const) && -> void override;
            virtual auto clone() const -> std::unique_ptr<Constraint> override;
        };
    }
}

#endif
