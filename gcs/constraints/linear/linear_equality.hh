#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_EQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_LINEAR_EQUALITY_HH

#include <gcs/constraint.hh>
#include <gcs/expression.hh>
#include <gcs/innards/literal.hh>

namespace gcs
{
    /**
     * \brief Constrain that the sum of the variables multiplied by their associated
     * coefficients is equal to the specified value, if and only if a condition holds.
     *
     * If gac is specifed, achieves generalised arc consistency. This is very
     * expensive for large variables.
     *
     * \ingroup Constraints
     * \sa LinearLessEqual
     * \sa LinearGreaterThanEqual
     * \sa LinearEquality
     */
    class LinearEqualityIff : public Constraint
    {
    private:
        WeightedSum _coeff_vars;
        Integer _value;
        innards::Literal _cond;
        bool _gac;

    public:
        explicit LinearEqualityIff(WeightedSum coeff_vars, Integer value, innards::Literal cond, bool gac = false);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

    class LinearEquality : public LinearEqualityIff
    {
    public:
        explicit LinearEquality(WeightedSum coeff_vars, Integer value, bool gac = false);
    };

    class LinearNotEquals : public LinearEqualityIff
    {
    public:
        explicit LinearNotEquals(WeightedSum coeff_vars, Integer value, bool gac = false);
    };
}

#endif
