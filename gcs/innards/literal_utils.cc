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

namespace
{
    auto is_literally_true_or_false(const Literal & lit) -> optional<bool>
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

auto gcs::innards::sanitise_literals(Literals & lits) -> bool
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

auto gcs::innards::sanitise_pseudoboolean_ge(WeightedLiterals & lits, Integer & val) -> bool
{
    // adjust coefficients down for true and false literals
    for (auto l = lits.begin(), l_end = lits.end(); l != l_end; ++l) {
        auto t_or_f = is_literally_true_or_false(l->second);
        if (t_or_f && *t_or_f)
            val -= l->first;
        else if (t_or_f && ! *t_or_f)
            val += l->first;
    }

    // now actually remove true and false literals
    lits.erase(remove_if(lits.begin(), lits.end(), [&](const auto & wlit) -> bool { return nullopt != is_literally_true_or_false(wlit.second); }), lits.end());

    return true;
}
