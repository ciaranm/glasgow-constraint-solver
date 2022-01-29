/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "util/overloaded.hh"
#include <gcs/variable_id.hh>

using namespace gcs;

using std::pair;
using std::string;
using std::to_string;
using std::visit;

auto gcs::debug_string(const IntegerVariableID & var) -> string
{
    return overloaded(
        [](SimpleIntegerVariableID x) {
            return "varidx " + to_string(x.index);
        },
        [](ViewOfIntegerVariableID x) {
            return "view " + debug_string(VariableID{x.actual_variable}) + " offset " + to_string(x.offset.raw_value);
        },
        [](ConstantIntegerVariableID x) {
            return "const " + to_string(x.const_value.raw_value);
        })
        .visit(var);
}

auto gcs::debug_string(const VariableID & var) -> string
{
    return overloaded(
        [](IntegerVariableID v) { return "int " + debug_string(v); })
        .visit(var);
}

auto gcs::underlying_direct_variable_and_offset(const IntegerVariableID var) -> pair<DirectIntegerVariableID, Integer>
{
    return overloaded(
        [&](const SimpleIntegerVariableID & v) -> pair<DirectIntegerVariableID, Integer> {
            return pair{v, 0_i};
        },
        [&](const ConstantIntegerVariableID & v) -> pair<DirectIntegerVariableID, Integer> {
            return pair{v, 0_i};
        },
        [&](const ViewOfIntegerVariableID & v) -> pair<DirectIntegerVariableID, Integer> {
            return pair{v.actual_variable, v.offset};
        })
        .visit(var);
}

auto gcs::operator+(IntegerVariableID v, Integer o) -> IntegerVariableID
{
    return overloaded(
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableID { return ViewOfIntegerVariableID{v, o}; },
        [&](const ConstantIntegerVariableID & v) -> IntegerVariableID { return ConstantIntegerVariableID{v.const_value + o}; },
        [&](const ViewOfIntegerVariableID & v) -> IntegerVariableID { return ViewOfIntegerVariableID{v.actual_variable, v.offset + o}; })
        .visit(v);
}

auto gcs::operator-(IntegerVariableID v, Integer o) -> IntegerVariableID
{
    return overloaded(
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableID { return ViewOfIntegerVariableID{v, -o}; },
        [&](const ConstantIntegerVariableID & v) -> IntegerVariableID { return ConstantIntegerVariableID{v.const_value - o}; },
        [&](const ViewOfIntegerVariableID & v) -> IntegerVariableID { return ViewOfIntegerVariableID{v.actual_variable, v.offset - o}; })
        .visit(v);
}
