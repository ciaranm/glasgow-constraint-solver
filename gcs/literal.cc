#include <gcs/exception.hh>
#include <gcs/literal.hh>

#include <util/overloaded.hh>

using namespace gcs;

auto gcs::operator!(const LiteralFromIntegerVariable & ilit) -> LiteralFromIntegerVariable
{
    switch (ilit.op) {
    case LiteralOperator::Equal:
        return LiteralFromIntegerVariable{ilit.var, LiteralOperator::NotEqual, ilit.value};
    case LiteralOperator::NotEqual:
        return LiteralFromIntegerVariable{ilit.var, LiteralOperator::Equal, ilit.value};
    case LiteralOperator::Less:
        return LiteralFromIntegerVariable{ilit.var, LiteralOperator::GreaterEqual, ilit.value};
    case LiteralOperator::GreaterEqual:
        return LiteralFromIntegerVariable{ilit.var, LiteralOperator::Less, ilit.value};
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
