/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>
#include <gcs/literal.hh>

#include <util/overloaded.hh>

using namespace gcs;

auto gcs::operator!(const Literal & lit) -> Literal
{
    return overloaded{
        [](const LiteralFromIntegerVariable & ilit) {
            switch (ilit.op) {
                using enum LiteralFromIntegerVariable::Operator;
            case Equal:
                return Literal{LiteralFromIntegerVariable{ilit.var, NotEqual, ilit.value}};
            case NotEqual:
                return Literal{LiteralFromIntegerVariable{ilit.var, Equal, ilit.value}};
            case Less:
                return Literal{LiteralFromIntegerVariable{ilit.var, GreaterEqual, ilit.value}};
            case GreaterEqual:
                return Literal{LiteralFromIntegerVariable{ilit.var, Less, ilit.value}};
            }
            throw NonExhaustiveSwitch{};
        },
        [](const TrueLiteral &) -> Literal {
            return FalseLiteral{};
        },
        [](const FalseLiteral &) -> Literal {
            return TrueLiteral{};
        }}
        .visit(lit);
}
