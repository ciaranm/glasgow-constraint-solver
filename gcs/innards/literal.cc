#include <gcs/exception.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/variable_id_utils.hh>
#include <gcs/variable_id.hh>

#include <util/overloaded.hh>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::string;

auto gcs::innards::operator!(const Literal & lit) -> Literal
{
    return visit([&](const auto & f) { return Literal{! f}; }, lit);
}

auto gcs::innards::operator!(const TrueLiteral &) -> FalseLiteral
{
    return FalseLiteral{};
}

auto gcs::innards::operator!(const FalseLiteral &) -> TrueLiteral
{
    return TrueLiteral{};
}

auto gcs::innards::debug_string(const Literal & lit) -> string
{
    return overloaded{
        [](const IntegerVariableCondition & ilit) -> string {
            switch (ilit.op) {
            case VariableConditionOperator::Equal:
                return "intvars[" + debug_string(ilit.var) + "] = " + ilit.value.to_string();
            case VariableConditionOperator::NotEqual:
                return "intvars[" + debug_string(ilit.var) + "] != " + ilit.value.to_string();
            case VariableConditionOperator::GreaterEqual:
                return "intvars[" + debug_string(ilit.var) + "] >= " + ilit.value.to_string();
            case VariableConditionOperator::Less:
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

auto gcs::innards::debug_string(const Literals & lits) -> string
{
    string result = "literals(";
    for (auto & lit : lits)
        result += debug_string(lit) + " ";
    result += ")";
    return result;
}

auto gcs::innards::is_literally_true_or_false(const Literal & lit) -> optional<bool>
{
    return overloaded{
        [](const IntegerVariableCondition & ilit) -> optional<bool> {
            return overloaded{
                [&](SimpleIntegerVariableID) -> optional<bool> { return nullopt; },
                [&](ViewOfIntegerVariableID) -> optional<bool> { return nullopt; },
                [&](ConstantIntegerVariableID x) -> optional<bool> {
                    switch (ilit.op) {
                    case VariableConditionOperator::Equal: return x.const_value == ilit.value;
                    case VariableConditionOperator::NotEqual: return x.const_value != ilit.value;
                    case VariableConditionOperator::GreaterEqual: return x.const_value >= ilit.value;
                    case VariableConditionOperator::Less: return x.const_value < ilit.value;
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
