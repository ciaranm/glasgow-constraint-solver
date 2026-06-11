#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/simplify_literal.hh>

#include <util/overloaded.hh>

#include <algorithm>

using std::max;
using std::min;
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

    // Canonicalise a range condition (dev_docs/range_literals_spec.md §2): clamp
    // it to the variable's definition bounds (the bound axioms make the clamped
    // condition the same fact, and the partition's cells only span the definition
    // range), so a vacuous range folds to a constant, the whole range folds to a
    // constant (the whole-variable interval literal is never materialised), and a
    // width-1 range IS the eq atom. Everything downstream (need_proof_name,
    // xliteral_for) sees only interior, multi-width range conditions.
    template <typename VarType_>
    auto canonicalise_range(const NamesAndIDsTracker & tracker, VariableConditionFrom<VarType_> cond) -> SimpleLiteral
    {
        bool in = (VariableConditionOperator::InRange == cond.op);
        if (auto bounds = tracker.find_definition_bounds(cond.var)) {
            cond.value = max(cond.value, bounds->first);
            cond.upper_value = min(cond.upper_value, bounds->second);
            if (cond.value > cond.upper_value)
                return in ? SimpleLiteral{FalseLiteral{}} : SimpleLiteral{TrueLiteral{}};
            if (cond.value == bounds->first && cond.upper_value == bounds->second)
                return in ? SimpleLiteral{TrueLiteral{}} : SimpleLiteral{FalseLiteral{}};
        }
        if (cond.value == cond.upper_value)
            return VariableConditionFrom<VarType_>{cond.var,
                in ? VariableConditionOperator::Equal : VariableConditionOperator::NotEqual, cond.value};
        return cond;
    }

    auto is_range_op(VariableConditionOperator op) -> bool
    {
        return VariableConditionOperator::InRange == op || VariableConditionOperator::NotInRange == op;
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
                    auto cond = VariableConditionFrom<SimpleIntegerVariableID>{var, lit.op, lit.value, lit.upper_value};
                    if (is_range_op(lit.op))
                        return canonicalise_range(tracker, cond);
                    return cond;
                },
                [&](const ViewOfIntegerVariableID & view) -> SimpleLiteral {
                    // Range conditions on views take the per-value fallback at the
                    // producing sites (spec §9.1: folding views into the interval
                    // machinery is deferred), so none should reach the literal
                    // layer. A range literal on the view's proof-only variable
                    // would be an interval vocabulary unlinked to the underlying
                    // variable's, which is a silent replay-completeness hole; throw
                    // rather than risk it.
                    if (is_range_op(lit.op))
                        throw UnimplementedException{"range conditions on views are not yet supported"};

                    // If the view's proof-only variable is registered, emit
                    // the literal over V's own bits with op and value
                    // preserved verbatim - V represents the visible view
                    // value directly. Falls back to deviewing through the
                    // underlying when the view isn't in the registry
                    // (proof-logging-only path).
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
                    case VariableConditionOperator::InRange:
                    case VariableConditionOperator::NotInRange:
                        // unreachable: thrown above
                        throw UnimplementedException{"range conditions on views are not yet supported"};
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
                    case VariableConditionOperator::InRange:
                        return (cvar.const_value >= lit.value && cvar.const_value <= lit.upper_value) ? SimpleLiteral{TrueLiteral{}} : SimpleLiteral{FalseLiteral{}};
                    case VariableConditionOperator::NotInRange:
                        return (cvar.const_value < lit.value || cvar.const_value > lit.upper_value) ? SimpleLiteral{TrueLiteral{}} : SimpleLiteral{FalseLiteral{}};
                    }
                    throw NonExhaustiveSwitch{};
                }}
                .visit(lit.var);
        },
        [&](const ProofVariableCondition & cond) -> SimpleLiteral {
            auto result = VariableConditionFrom<ProofOnlySimpleIntegerVariableID>{cond.var, cond.op, cond.value, cond.upper_value};
            if (is_range_op(cond.op))
                return canonicalise_range(tracker, result);
            return result;
        }}
        .visit(flatten(lit));
}
