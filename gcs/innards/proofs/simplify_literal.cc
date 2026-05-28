#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/simplify_literal.hh>

#include <util/overloaded.hh>

using std::variant;

using namespace gcs;
using namespace gcs::innards;

namespace
{
    using FlattenedProofLiteral = variant<IntegerVariableCondition, TrueLiteral, FalseLiteral, ProofVariableCondition>;

    auto flatten(const ProofLiteral & lit) -> FlattenedProofLiteral
    {
        return overloaded{
            [&](const Literal & lit) {
                return visit([&](const auto & v) -> FlattenedProofLiteral { return v; }, lit);
            },
            [&](const ProofVariableCondition & cond) -> FlattenedProofLiteral {
                return cond;
            }}
            .visit(lit);
    }
}

auto gcs::innards::simplify_literal(const NamesAndIDsTracker & tracker, const ProofLiteral & lit) -> SimpleLiteral
{
    return overloaded{
        [&](const TrueLiteral & t) -> SimpleLiteral { return t; },
        [&](const FalseLiteral & f) -> SimpleLiteral { return f; },
        [&](const IntegerVariableCondition & lit) -> SimpleLiteral {
            return overloaded{
                [&](const SimpleIntegerVariableID & var) -> SimpleLiteral {
                    return VariableConditionFrom<SimpleIntegerVariableID>{var, lit.op, lit.value};
                },
                [&](const ViewOfIntegerVariableID & view) -> SimpleLiteral {
                    // Stage 3: if the view's proof-only variable is
                    // registered, emit the literal over V's own bits with
                    // op and value preserved verbatim - V represents the
                    // visible view value directly. Falls back to deviewing
                    // through the underlying when the view isn't in the
                    // registry (proof-logging-only path).
                    if (auto v_id = tracker.find_view(view))
                        return ProofVariableCondition{*v_id, lit.op, lit.value};
                    switch (lit.op) {
                    case VariableConditionOperator::NotEqual:
                        return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::NotEqual,
                            (view.negate_first ? -lit.value + view.then_add : lit.value - view.then_add)};
                        break;
                    case VariableConditionOperator::Equal:
                        return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::Equal,
                            view.negate_first ? -lit.value + view.then_add : lit.value - view.then_add};
                        break;
                    case VariableConditionOperator::Less:
                        if (view.negate_first)
                            return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::GreaterEqual,
                                -lit.value + view.then_add + 1_i};
                        else
                            return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::Less,
                                (lit.value - view.then_add)};
                        break;
                    case VariableConditionOperator::GreaterEqual:
                        if (view.negate_first)
                            return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::Less,
                                -lit.value + view.then_add + 1_i};
                        else
                            return VariableConditionFrom<SimpleIntegerVariableID>{view.actual_variable, VariableConditionOperator::GreaterEqual,
                                lit.value - view.then_add};
                        break;
                    }
                    throw NonExhaustiveSwitch{};
                },
                [&](const ConstantIntegerVariableID & cvar) -> SimpleLiteral {
                    switch (lit.op) {
                    case VariableConditionOperator::NotEqual:
                        return cvar.const_value != lit.value ? SimpleLiteral{TrueLiteral{}} : SimpleLiteral{FalseLiteral{}};
                    case VariableConditionOperator::Equal:
                        return cvar.const_value == lit.value ? SimpleLiteral{TrueLiteral{}} : SimpleLiteral{FalseLiteral{}};
                    case VariableConditionOperator::Less:
                        return cvar.const_value < lit.value ? SimpleLiteral{TrueLiteral{}} : SimpleLiteral{FalseLiteral{}};
                    case VariableConditionOperator::GreaterEqual:
                        return cvar.const_value >= lit.value ? SimpleLiteral{TrueLiteral{}} : SimpleLiteral{FalseLiteral{}};
                    }
                    throw NonExhaustiveSwitch{};
                }}
                .visit(lit.var);
        },
        [&](const ProofVariableCondition & cond) -> SimpleLiteral {
            return VariableConditionFrom<ProofOnlySimpleIntegerVariableID>{cond.var, cond.op, cond.value};
        }}
        .visit(flatten(lit));
}
