/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/detail/variable_id_utils.hh>

#include <util/overloaded.hh>

#include <string>

using namespace gcs;

using std::pair;
using std::string;
using std::to_string;

auto gcs::debug_string(const IntegerVariableID & var) -> string
{
    return overloaded{
        [](SimpleIntegerVariableID x) {
            return "varidx " + to_string(x.index);
        },
        [](ViewOfIntegerVariableID x) {
            return "view " + debug_string(VariableID{x.actual_variable}) + " offset " + to_string(x.offset.raw_value);
        },
        [](ConstantIntegerVariableID x) {
            return "const " + to_string(x.const_value.raw_value);
        }}
        .visit(var);
}

auto gcs::debug_string(const VariableID & var) -> string
{
    return overloaded{
        [](IntegerVariableID v) { return "int " + debug_string(v); }}
        .visit(var);
}

auto gcs::underlying_direct_variable_and_offset(const IntegerVariableID & var) -> pair<DirectIntegerVariableID, Integer>
{
    return visit([&](const auto & var) -> pair<DirectIntegerVariableID, Integer> { return underlying_direct_variable_and_offset(var); }, var);
}

auto gcs::underlying_direct_variable_and_offset(const DirectIntegerVariableID & var) -> pair<DirectIntegerVariableID, Integer>
{
    return visit([&](const auto & var) -> pair<DirectIntegerVariableID, Integer> { return underlying_direct_variable_and_offset(var); }, var);
}
