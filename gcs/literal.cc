/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>
#include <gcs/literal.hh>

#include <util/overloaded.hh>

#include <optional>

using namespace gcs;

using std::nullopt;
using std::optional;
using std::remove_if;
using std::string;
using std::unique;
using std::visit;

auto gcs::debug_string(const Literal & lit) -> string
{
    return overloaded(
        [](const LiteralFromIntegerVariable & ilit) -> string {
            switch (ilit.op) {
                using enum LiteralFromIntegerVariable::Operator;
            case Equal:
                return "intvars[" + debug_string(ilit.var) + "] = " + ilit.value.to_string();
            case NotEqual:
                return "intvars[" + debug_string(ilit.var) + "] != " + ilit.value.to_string();
            case GreaterEqual:
                return "intvars[" + debug_string(ilit.var) + "] >= " + ilit.value.to_string();
            case Less:
                return "intvars[" + debug_string(ilit.var) + "] < " + ilit.value.to_string();
            }
            throw NonExhaustiveSwitch{};
        },
        [](const TrueLiteral &) -> string {
            return "true";
        },
        [](const FalseLiteral &) -> string {
            return "false";
        })
        .visit(lit);
}

namespace
{
    auto is_literally_true_or_false(const Literal & lit) -> optional<bool>
    {
        return overloaded(
            [](const LiteralFromIntegerVariable & ilit) -> optional<bool> {
                return overloaded(
                    [&](SimpleIntegerVariableID) -> optional<bool> { return nullopt; },
                    [&](ViewOfIntegerVariableID) -> optional<bool> { return nullopt; },
                    [&](ConstantIntegerVariableID x) -> optional<bool> {
                        switch (ilit.op) {
                            using enum LiteralFromIntegerVariable::Operator;
                        case Equal: return x.const_value == ilit.value;
                        case NotEqual: return x.const_value != ilit.value;
                        case GreaterEqual: return x.const_value >= ilit.value;
                        case Less: return x.const_value < ilit.value;
                        }
                        throw NonExhaustiveSwitch{};
                    })
                    .visit(ilit.var);
            },
            [](const TrueLiteral &) -> optional<bool> {
                return true;
            },
            [](const FalseLiteral &) -> optional<bool> {
                return false;
            })
            .visit(lit);
    }
}

auto gcs::is_literally_true(const Literal & lit) -> bool
{
    auto result = is_literally_true_or_false(lit);
    return result && *result;
}

auto gcs::is_literally_false(const Literal & lit) -> bool
{
    auto result = is_literally_true_or_false(lit);
    return result && ! *result;
}

auto gcs::sanitise_literals(Literals & lits) -> bool
{
    // if we've got a literal that is definitely true, the clause is always satisfied,
    // so we can discard the clause
    if (lits.end() != find_if(lits.begin(), lits.end(), [](const Literal & lit) -> bool { return is_literally_true(lit); }))
        return false;

    // remove any literals that are definitely false. this might remove everything, in
    // which case we get the empty clause which is false so it's fine.
    lits.erase(remove_if(lits.begin(), lits.end(), [&](const Literal & lit) -> bool { return is_literally_false(lit); }), lits.end());

    // put these in some kind of order
    sort(lits.begin(), lits.end());

    // remove duplicates
    lits.erase(unique(lits.begin(), lits.end()), lits.end());

    return true;
}

auto gcs::operator!(const Literal & lit) -> Literal
{
    return overloaded(
        [](const LiteralFromIntegerVariable & ilit) {
            switch (ilit.op) {
                using enum LiteralFromIntegerVariable::Operator;
            case Equal:
                return Literal{LiteralFromIntegerVariable{ilit.var, NotEqual, ilit.value}};
            case NotEqual:
                return Literal{LiteralFromIntegerVariable{ilit.var, Equal, ilit.value}};
            case Less:
                return Literal{LiteralFromIntegerVariable{ilit.var, GreaterEqual, ilit.value}};
            case GreaterEqual:
                return Literal{LiteralFromIntegerVariable{ilit.var, Less, ilit.value}};
            }
            throw NonExhaustiveSwitch{};
        },
        [](const TrueLiteral &) -> Literal {
            return FalseLiteral{};
        },
        [](const FalseLiteral &) -> Literal {
            return TrueLiteral{};
        })
        .visit(lit);
}
