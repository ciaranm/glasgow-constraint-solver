/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>
#include <gcs/innards/literal_utils.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <util/overloaded.hh>

#include <optional>

using namespace gcs;

using std::nullopt;
using std::optional;
using std::remove_if;
using std::string;
using std::unique;

auto gcs::innards::debug_string(const Literal & lit) -> string
{
    return overloaded{
        [](const LiteralFromIntegerVariable & ilit) -> string {
            switch (ilit.op) {
            case LiteralFromIntegerVariable::Operator::Equal:
                return "intvars[" + debug_string(ilit.var) + "] = " + ilit.value.to_string();
            case LiteralFromIntegerVariable::Operator::NotEqual:
                return "intvars[" + debug_string(ilit.var) + "] != " + ilit.value.to_string();
            case LiteralFromIntegerVariable::Operator::GreaterEqual:
                return "intvars[" + debug_string(ilit.var) + "] >= " + ilit.value.to_string();
            case LiteralFromIntegerVariable::Operator::Less:
                return "intvars[" + debug_string(ilit.var) + "] < " + ilit.value.to_string();
            }
            throw NonExhaustiveSwitch{};
        },
        [](const TrueLiteral &) -> string {
            return "true";
        },
        [](const FalseLiteral &) -> string {
            return "false";
        }}
        .visit(lit);
}

auto gcs::innards::is_literally_true_or_false(const Literal & lit) -> optional<bool>
{
    return overloaded{
        [](const LiteralFromIntegerVariable & ilit) -> optional<bool> {
            return overloaded{
                [&](SimpleIntegerVariableID) -> optional<bool> { return nullopt; },
                [&](ViewOfIntegerVariableID) -> optional<bool> { return nullopt; },
                [&](ConstantIntegerVariableID x) -> optional<bool> {
                    switch (ilit.op) {
                    case LiteralFromIntegerVariable::Operator::Equal: return x.const_value == ilit.value;
                    case LiteralFromIntegerVariable::Operator::NotEqual: return x.const_value != ilit.value;
                    case LiteralFromIntegerVariable::Operator::GreaterEqual: return x.const_value >= ilit.value;
                    case LiteralFromIntegerVariable::Operator::Less: return x.const_value < ilit.value;
                    }
                    throw NonExhaustiveSwitch{};
                }}
                .visit(ilit.var);
        },
        [](const TrueLiteral &) -> optional<bool> {
            return true;
        },
        [](const FalseLiteral &) -> optional<bool> {
            return false;
        }}
        .visit(lit);
}

auto gcs::innards::is_literally_true(const Literal & lit) -> bool
{
    auto result = is_literally_true_or_false(lit);
    return result && *result;
}

auto gcs::innards::is_literally_false(const Literal & lit) -> bool
{
    auto result = is_literally_true_or_false(lit);
    return result && ! *result;
}
