/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "util/overloaded.hh"
#include <gcs/variable_id.hh>

using namespace gcs;

using std::pair;
using std::string;
using std::to_string;

auto gcs::operator+(IntegerVariableID v, Integer o) -> IntegerVariableID
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableID { return ViewOfIntegerVariableID{v, o}; },
        [&](const ConstantIntegerVariableID & v) -> IntegerVariableID { return ConstantIntegerVariableID{v.const_value + o}; },
        [&](const ViewOfIntegerVariableID & v) -> IntegerVariableID { return ViewOfIntegerVariableID{v.actual_variable, v.offset + o}; }}
        .visit(v);
}

auto gcs::operator-(IntegerVariableID v, Integer o) -> IntegerVariableID
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableID { return ViewOfIntegerVariableID{v, -o}; },
        [&](const ConstantIntegerVariableID & v) -> IntegerVariableID { return ConstantIntegerVariableID{v.const_value - o}; },
        [&](const ViewOfIntegerVariableID & v) -> IntegerVariableID { return ViewOfIntegerVariableID{v.actual_variable, v.offset - o}; }}
        .visit(v);
}
