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
    class LinearLessThanEqual : public innards::LinearInequalityIff
    {
    public:
        explicit LinearLessThanEqual(WeightedSum coeff_vars, Integer value);
    };

    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is less than or equal to the specified value,
     * if a condition holds.
     *
     * \ingroup innards
     * \sa LinearLessThanEqual
     */
    class LinearLessThanEqualIf : public innards::LinearInequalityIf
    {
    public:
        explicit LinearLessThanEqualIf(WeightedSum coeff_vars, Integer value, innards::Literal cond);
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
    class LinearLessThanEqualIff : public innards::LinearInequalityIff
    {
    public:
        explicit LinearLessThanEqualIff(WeightedSum coeff_vars, Integer value, innards::Literal cond);
    };
}

#endif
