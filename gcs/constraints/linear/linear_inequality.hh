#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_INEQUALITY_HH 1

#include <gcs/constraint.hh>
#include <gcs/expression.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>

#include <memory>

namespace gcs
{
    namespace innards
    {
        /**
         * \brief Constrain that the sum of the variables multiplied by their
         * associated coefficients is either less than or equal to, or greater than
         * or equal to, the specified value.
         *
         * \ingroup innards
         * \sa LinearLessEqual
         * \sa LinearGreaterThanEqual
         */
        class LinearInequality : public Constraint
        {
        private:
            WeightedSum _coeff_vars;
            Integer _value;

        public:
            explicit LinearInequality(WeightedSum coeff_vars, Integer value);

            virtual auto install(innards::Propagators &, innards::State &) && -> void override;
            virtual auto describe_for_proof() -> std::string override;
            virtual auto clone() const -> std::unique_ptr<Constraint> override;
        };
    }
}

#endif
