/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>
#include <gcs/literal.hh>

#include <util/overloaded.hh>

using namespace gcs;

auto gcs::operator!(const LiteralFromIntegerVariable & ilit) -> LiteralFromIntegerVariable
{
    switch (ilit.op) {
    using enum LiteralFromIntegerVariable::Operator;
    case Equal:
        return LiteralFromIntegerVariable{ilit.var, NotEqual, ilit.value};
    case NotEqual:
        return LiteralFromIntegerVariable{ilit.var, Equal, ilit.value};
    case Less:
        return LiteralFromIntegerVariable{ilit.var, GreaterEqual, ilit.value};
    case GreaterEqual:
        return LiteralFromIntegerVariable{ilit.var, Less, ilit.value};
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
