#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_GREATER_EQUAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_GREATER_EQUAL_HH

#include <gcs/constraints/linear/linear_inequality.hh>

namespace gcs
{
    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is greater than or equal to the specified value.
     *
     * \ingroup innards
     * \sa LinearEquality
     * \sa LinearLessEqual
     */
    class LinearGreaterThanEqual : public innards::LinearInequalityIff
    {
    public:
        explicit LinearGreaterThanEqual(WeightedSum coeff_vars, Integer value);
    };

    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is greater than or equal to the specified value,
     * if and only if a condition holds.
     *
     * \ingroup innards
     * \sa LinearEquality
     * \sa LinearLessEqual
     */
    class LinearGreaterThanEqualIff : public innards::LinearInequalityIff
    {
    public:
        explicit LinearGreaterThanEqualIff(WeightedSum coeff_vars, Integer value, innards::Literal cond);
    };
}

#endif
