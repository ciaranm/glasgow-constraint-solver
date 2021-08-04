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
            [] (unsigned long long x) { return to_string(x); },
            [] (Integer x)            { return "const " + to_string(x.raw_value); }
            }, var.index_or_const_value);
}

auto gcs::debug_string(const BooleanVariableID & var) -> string
{
    return visit(overloaded {
            [] (unsigned long long x) { return to_string(x); },
            [] (Integer x)            { return "const " + to_string(x.raw_value); }
            }, var.index_or_const_value);
}

auto gcs::debug_string(const VariableID & var) -> string
{
    return visit(overloaded{
            [] (IntegerVariableID v) { return "int " + debug_string(v); },
            [] (BooleanVariableID v) { return "bool " + debug_string(v); }
            }, var);
}

