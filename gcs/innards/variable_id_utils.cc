#include <gcs/innards/variable_id_utils.hh>

#include <util/overloaded.hh>

#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::string;
using std::to_string;

using namespace std::literals::string_literals;

auto gcs::innards::debug_string(const IntegerVariableID & var) -> string
{
    return overloaded{
        [](SimpleIntegerVariableID x) {
            return "varidx " + to_string(x.index);
        },
        [](ViewOfIntegerVariableID x) {
            return "view " + (x.negate_first ? "-"s : ""s) + debug_string(VariableID{x.actual_variable}) + " + " + to_string(x.then_add.raw_value);
        },
        [](ConstantIntegerVariableID x) {
            return "const " + to_string(x.const_value.raw_value);
        }}
        .visit(var);
}

auto gcs::innards::debug_string(const VariableID & var) -> string
{
    return overloaded{
        [](IntegerVariableID v) { return "int " + debug_string(v); }}
        .visit(var);
}
