/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ARITHMETIC_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ARITHMETIC_HH 1

#include <gcs/constraint.hh>
#include <gcs/integer_variable.hh>

namespace gcs
{
    enum class ArithmeticOperator
    {
        Plus,
        Times,
        Div,
        Mod,
        Power
    };

    template <ArithmeticOperator op_>
    class Arithmetic :
        public Constraint
    {
        private:
            IntegerVariableID _v1, _v2, _result;

        public:
            explicit Arithmetic(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result);

            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void override;
    };

    using Plus = Arithmetic<ArithmeticOperator::Plus>;
    using Times = Arithmetic<ArithmeticOperator::Times>;
    using Div = Arithmetic<ArithmeticOperator::Div>;
    using Mod = Arithmetic<ArithmeticOperator::Mod>;
    using Power = Arithmetic<ArithmeticOperator::Power>;
}

#endif
