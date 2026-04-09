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
     * \sa LinearLessThanEqual
     */
    class LinearGreaterThanEqual : public ReifiedLinearInequality
    {
    public:
        explicit LinearGreaterThanEqual(WeightedSum coeff_vars, Integer value);
    };

    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is greater than or equal to the specified value,
     * if a condition holds.
     *
     * \ingroup innards
     * \sa LinearGreaterThanEqual
     */
    class LinearGreaterThanEqualIf : public ReifiedLinearInequality
    {
    public:
        explicit LinearGreaterThanEqualIf(WeightedSum coeff_vars, Integer value, IntegerVariableCondition cond);
    };

    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is greater than or equal to the specified value,
     * if and only if a condition holds.
     *
     * \ingroup innards
     * \sa LinearEquality
     * \sa LinearLessThanEqual
     */
    class LinearGreaterThanEqualIff : public ReifiedLinearInequality
    {
    public:
        explicit LinearGreaterThanEqualIff(WeightedSum coeff_vars, Integer value, IntegerVariableCondition cond);
    };
}

#endif
