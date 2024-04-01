#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_LESS_EQUAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_LESS_EQUAL_HH

#include <gcs/constraints/linear/linear_inequality.hh>

namespace gcs
{
    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is less than or equal to the specified value.
     *
     * \ingroup innards
     * \sa LinearEquality
     * \sa LinearGreaterThanEqual
     */
    class LinearLessEqual : public innards::LinearInequalityIff
    {
    public:
        explicit LinearLessEqual(WeightedSum coeff_vars, Integer value);
    };

    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is less than or equal to the specified value,
     * if and only if a condition holds.
     *
     * \ingroup innards
     * \sa LinearEquality
     * \sa LinearGreaterThanEqual
     */
    class LinearLessEqualIff : public innards::LinearInequalityIff
    {
    public:
        explicit LinearLessEqualIff(WeightedSum coeff_vars, Integer value, innards::Literal cond);
    };
}

#endif
