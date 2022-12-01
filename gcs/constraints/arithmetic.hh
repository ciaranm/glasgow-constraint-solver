/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ARITHMETIC_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ARITHMETIC_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

namespace gcs
{
    namespace innards
    {
        enum class ArithmeticOperator
        {
            Plus,
            Minus,
            Times,
            Div,
            Mod,
            Power
        };

        /**
         * \brief Arithmetic constraint, constraints that `v1 op v2 = result`.
         *
         * \ingroup Constraints
         * \ingroup Innards
         * \sa gcs::Plus
         * \sa gcs::Minus
         * \sa gcs::Times
         * \sa gcs::Div
         * \sa gcs::Mod
         * \sa gcs::Power
         */
        template <ArithmeticOperator op_>
        class GACArithmetic : public Constraint
        {
        private:
            IntegerVariableID _v1, _v2, _result;

        public:
            explicit GACArithmetic(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result);

            virtual auto describe_for_proof() -> std::string override;
            virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
            virtual auto clone() const -> std::unique_ptr<Constraint> override;
        };
    }

    /**
     * \brief Constrain that `v1 + v2 = result`.
     *
     * \ingroup Constraints
     */
    using Plus = innards::GACArithmetic<innards::ArithmeticOperator::Plus>;

    /**
     * \brief Constrain that `v1 - v2 = result`.
     *
     * \ingroup Constraints
     */
    using Minus = innards::GACArithmetic<innards::ArithmeticOperator::Minus>;

    /**
     * \brief Constrain that `v1 * v2 = result`.
     *
     * \ingroup Constraints
     */
    using Times = innards::GACArithmetic<innards::ArithmeticOperator::Times>;

    /**
     * \brief Constrain that `v1 / v2 = result`.
     *
     * \ingroup Constraints
     */
    using Div = innards::GACArithmetic<innards::ArithmeticOperator::Div>;

    /**
     * \brief Constrain that `v1 % v2 = result`.
     *
     * \ingroup Constraints
     */
    using Mod = innards::GACArithmetic<innards::ArithmeticOperator::Mod>;

    /**
     * \brief Constrain that `power(v1, v2) = result`.
     *
     * \ingroup Constraints
     */
    using Power = innards::GACArithmetic<innards::ArithmeticOperator::Power>;
}

#endif
