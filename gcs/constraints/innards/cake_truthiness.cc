#include <gcs/constraints/innards/cake_truthiness.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/s_expr.hh>

#include <util/overloaded.hh>

#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::nullopt;
using std::optional;
using std::pair;
using std::vector;

auto gcs::innards::cake_positive_form(const Literal & lit, const function<pair<Integer, Integer>(const SimpleIntegerVariableID &)> & bounds_of)
    -> optional<IntegerVariableID>
{
    return overloaded{[](const TrueLiteral &) -> optional<IntegerVariableID> { return IntegerVariableID{1_c}; },
        [](const FalseLiteral &) -> optional<IntegerVariableID> { return IntegerVariableID{0_c}; },
        [&](const IntegerVariableCondition & cond) -> optional<IntegerVariableID> {
            return overloaded{[&](const SimpleIntegerVariableID & var) -> optional<IntegerVariableID> {
                                  auto [lower, upper] = bounds_of(var);
                                  using enum VariableConditionOperator;
                                  switch (cond.op) {
                                  case NotEqual:
                                      if (0_i == cond.value && lower >= 0_i)
                                          return IntegerVariableID{var};
                                      return nullopt;
                                  case GreaterEqual:
                                      if (1_i == cond.value && lower >= 0_i)
                                          return IntegerVariableID{var};
                                      return nullopt;
                                  case Equal:
                                      if (1_i == cond.value && lower >= 0_i && upper <= 1_i)
                                          return IntegerVariableID{var};
                                      return nullopt;
                                  case Less: return nullopt;
                                  }
                                  return nullopt;
                              },
                [&](const ConstantIntegerVariableID & var) -> optional<IntegerVariableID> {
                    // A condition over a constant is statically valued.
                    using enum VariableConditionOperator;
                    bool holds = false;
                    switch (cond.op) {
                    case Equal: holds = var.const_value == cond.value; break;
                    case NotEqual: holds = var.const_value != cond.value; break;
                    case GreaterEqual: holds = var.const_value >= cond.value; break;
                    case Less: holds = var.const_value < cond.value; break;
                    }
                    return IntegerVariableID{holds ? 1_c : 0_c};
                },
                [](const ViewOfIntegerVariableID &) -> optional<IntegerVariableID> { return nullopt; }}
                .visit(cond.var);
        }}
        .visit(lit);
}

auto gcs::innards::cake_positive_literal(const IntegerVariableID & form) -> Literal
{
    return overloaded{[](const ConstantIntegerVariableID & c) -> Literal {
                          if (c.const_value >= 1_i)
                              return TrueLiteral{};
                          return FalseLiteral{};
                      },
        [](const SimpleIntegerVariableID & var) -> Literal { return var >= 1_i; },
        [](const ViewOfIntegerVariableID & var) -> Literal { return var >= 1_i; }}
        .visit(form);
}

auto gcs::innards::faithful_literal_term(const Literal & lit, const NamesAndIDsTracker & tracker) -> SExpr
{
    return overloaded{[](const TrueLiteral &) -> SExpr { return SExpr::atom("1"); }, [](const FalseLiteral &) -> SExpr { return SExpr::atom("0"); },
        [&](const IntegerVariableCondition & cond) -> SExpr {
            return SExpr::list(
                vector<SExpr>{tracker.s_expr_term_of(cond.var), SExpr::atom(tracker.s_expr_name_of(cond.op)), SExpr::atom(cond.value.to_string())});
        }}
        .visit(lit);
}
