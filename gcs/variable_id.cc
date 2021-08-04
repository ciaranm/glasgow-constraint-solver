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


