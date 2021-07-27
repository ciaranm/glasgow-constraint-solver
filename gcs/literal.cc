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
                    case LiteralFromIntegerVariable::Equal:        return "intvars[" + debug_string(ilit.var) + "] = " + to_string(ilit.value.raw_value);
                    case LiteralFromIntegerVariable::NotEqual:     return "intvars[" + debug_string(ilit.var) + "] != " + to_string(ilit.value.raw_value);
                    case LiteralFromIntegerVariable::GreaterEqual: return "intvars[" + debug_string(ilit.var) + "] >= " + to_string(ilit.value.raw_value);
                    case LiteralFromIntegerVariable::Less:         return "intvars[" + debug_string(ilit.var) + "] < " + to_string(ilit.value.raw_value);
                }
                throw NonExhaustiveSwitch{ };
            },
            [] (const LiteralFromBooleanVariable &) -> string {
                throw UnimplementedException{ };
            }
            }, lit);
}

auto gcs::sanitise_literals(Literals & lits) -> void
{
    sort(lits.begin(), lits.end(), [] (const Literal & a, const Literal & b) {
            return visit(overloaded {
                    [] (const LiteralFromBooleanVariable & a, const LiteralFromBooleanVariable & b) {
                        return a.var.index < b.var.index;
                    },
                    [] (const LiteralFromIntegerVariable & a, const LiteralFromIntegerVariable & b) {
                        return a.var.index_or_const_value < b.var.index_or_const_value;
                    },
                    [] (const LiteralFromBooleanVariable &, const LiteralFromIntegerVariable &) {
                        return true;
                    },
                    [] (const LiteralFromIntegerVariable &, const LiteralFromBooleanVariable &) {
                        return false;
                    }
                    }, a, b);
            });
}

