#include <gcs/exception.hh>
#include <gcs/variable_condition.hh>

using namespace gcs;

auto gcs::operator!(const IntegerVariableCondition & ilit) -> IntegerVariableCondition
{
    switch (ilit.op) {
    case VariableConditionOperator::Equal:
        return IntegerVariableCondition{ilit.var, VariableConditionOperator::NotEqual, ilit.value};
    case VariableConditionOperator::NotEqual:
        return IntegerVariableCondition{ilit.var, VariableConditionOperator::Equal, ilit.value};
    case VariableConditionOperator::Less:
        return IntegerVariableCondition{ilit.var, VariableConditionOperator::GreaterEqual, ilit.value};
    case VariableConditionOperator::GreaterEqual:
        return IntegerVariableCondition{ilit.var, VariableConditionOperator::Less, ilit.value};
    }
    throw NonExhaustiveSwitch{};
}
