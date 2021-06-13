/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/literal.hh"
#include "gcs/exception.hh"
#include "util/overloaded.hh"

using namespace gcs;

using std::string;
using std::to_string;
using std::visit;

auto gcs::debug_string(const Literal & lit) -> string
{
    return visit(overloaded {
            [] (const LiteralFromIntegerVariable & ilit) -> string {
                switch (ilit.state) {
                    case LiteralFromIntegerVariable::Equal:        return "intvars[" + to_string(ilit.var.index) + "] = " + to_string(ilit.value.raw_value);
                    case LiteralFromIntegerVariable::NotEqual:     return "intvars[" + to_string(ilit.var.index) + "] != " + to_string(ilit.value.raw_value);
                    case LiteralFromIntegerVariable::GreaterEqual: return "intvars[" + to_string(ilit.var.index) + "] >= " + to_string(ilit.value.raw_value);
                    case LiteralFromIntegerVariable::Less:         return "intvars[" + to_string(ilit.var.index) + "] < " + to_string(ilit.value.raw_value);
                }
                throw NonExhaustiveSwitch{ };
            },
            [] (const LiteralFromBooleanVariable &) -> string {
                throw UnimplementedException{ };
            }
            }, lit);
}

