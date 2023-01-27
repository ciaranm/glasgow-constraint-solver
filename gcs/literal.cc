#include <gcs/exception.hh>
#include <gcs/literal.hh>

#include <util/overloaded.hh>

using namespace gcs;

auto gcs::operator!(const LiteralFromIntegerVariable & ilit) -> LiteralFromIntegerVariable
{
    switch (ilit.op) {
    case LiteralFromIntegerVariable::Operator::Equal:
        return LiteralFromIntegerVariable{ilit.var, LiteralFromIntegerVariable::Operator::NotEqual, ilit.value};
    case LiteralFromIntegerVariable::Operator::NotEqual:
        return LiteralFromIntegerVariable{ilit.var, LiteralFromIntegerVariable::Operator::Equal, ilit.value};
    case LiteralFromIntegerVariable::Operator::Less:
        return LiteralFromIntegerVariable{ilit.var, LiteralFromIntegerVariable::Operator::GreaterEqual, ilit.value};
    case LiteralFromIntegerVariable::Operator::GreaterEqual:
        return LiteralFromIntegerVariable{ilit.var, LiteralFromIntegerVariable::Operator::Less, ilit.value};
    }
    throw NonExhaustiveSwitch{};
}

auto gcs::operator!(const Literal & lit) -> Literal
{
    return overloaded{
        [](const LiteralFromIntegerVariable & ilit) {
            return Literal{! ilit};
        },
        [](const TrueLiteral &) -> Literal {
            return FalseLiteral{};
        },
        [](const FalseLiteral &) -> Literal {
            return TrueLiteral{};
        }}
        .visit(lit);
}
