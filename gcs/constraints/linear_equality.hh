/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_EQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_EQUALITY_HH

#include <gcs/constraint.hh>
#include <gcs/integer.hh>
#include <gcs/linear.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the sum of the variables multiplied by their associated
     * coefficients is equal to the specified value.
     *
     * If gac is specifed, achieves generalised arc consistency. This is very
     * expensive for large variables.
     *
     * \ingroup Constraints
     */
    class LinearEquality : public Constraint
    {
    private:
        Linear _coeff_vars;
        Integer _value;
        bool _gac;

    public:
        explicit LinearEquality(Linear && coeff_vars, Integer value, bool gac = false);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };

    /**
     * \brief Constrain that the sum of the variables multiplied by their associated
     * coefficients is less than or equal to the specified value.
     *
     * \ingroup Constraints
     */
    class LinearLessEqual : public Constraint
    {
    private:
        Linear _coeff_vars;
        Integer _value;

    public:
        explicit LinearLessEqual(Linear && coeff_vars, Integer value);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };
}

#endif
