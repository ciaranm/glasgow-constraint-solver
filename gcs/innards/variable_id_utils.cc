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
            return "view " + (x.negate_first ? "-"s : ""s) + debug_string(x.actual_variable) + " + " + x.then_add.to_string();
        },
        [](ConstantIntegerVariableID x) {
            return "const " + x.const_value.to_string();
        }}
        .visit(var);
}
