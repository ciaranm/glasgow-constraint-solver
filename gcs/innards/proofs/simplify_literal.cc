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

auto gcs::innards::simplify_literal(NamesAndIDsTracker & tracker, const ProofLiteral & lit) -> SimpleLiteral
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
                    // Route through the extension: the literal `view op value`
                    // becomes `extension(view) op value` with no value adjustment,
                    // because the extension's value IS the view's value.
                    auto ext = tracker.extension_for(view);
                    return ProofVariableCondition{ext, lit.op, lit.value};
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
