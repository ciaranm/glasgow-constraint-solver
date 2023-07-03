#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_EQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_EQUALITY_HH

#include <gcs/constraint.hh>
#include <gcs/expression.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

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
     * \sa LinearLessEqual
     * \sa LinearGreaterThanEqual
     */
    class LinearEquality : public Constraint
    {
    private:
        WeightedSum _coeff_vars;
        Integer _value;
        bool _gac;

    public:
        explicit LinearEquality(WeightedSum coeff_vars, Integer value, bool gac = false);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

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

    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is less than or equal to the specified value.
     *
     * \ingroup innards
     * \sa LinearEquality
     * \sa LinearGreaterThanEqual
     */
    class LinearLessEqual : public innards::LinearInequality
    {
    public:
        explicit LinearLessEqual(WeightedSum coeff_vars, Integer value);
    };

    /**
     * \brief Constrain that the sum of the variables multiplied by their
     * associated coefficients is greater than or equal to the specified value.
     *
     * \ingroup innards
     * \sa LinearEquality
     * \sa LinearLessEqual
     */
    class LinearGreaterThanEqual : public innards::LinearInequality
    {
    public:
        explicit LinearGreaterThanEqual(WeightedSum coeff_vars, Integer value);
    };
}

#endif
