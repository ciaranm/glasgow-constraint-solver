/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/variable_id.hh>
#include "util/overloaded.hh"

using namespace gcs;

using std::string;
using std::to_string;
using std::visit;

auto gcs::debug_string(const IntegerVariableID & var) -> string
{
    return visit(overloaded {
            [] (SimpleIntegerVariableID x) { return "varidx " + to_string(x.index); },
            [] (ConstantIntegerVariableID x) { return "const " + to_string(x.const_value.raw_value); }
            }, var);
}

auto gcs::debug_string(const VariableID & var) -> string
{
    return visit(overloaded{
            [] (IntegerVariableID v) { return "int " + debug_string(v); }
            }, var);
}

