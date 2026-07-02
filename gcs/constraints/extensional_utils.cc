#include <cmath>
#include <gcs/constraints/extensional_utils.hh>
#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/multiply/hints.hh>
#include <gcs/constraints/table/hints.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/proof.hh>

using std::vector;
using std::visit;

using namespace gcs;
using namespace gcs::innards;

namespace
{
    auto feasible(const State & state, const IntegerVariableID & var, const Integer val) -> bool
    {
        return state.in_domain(var, val);
    }

    auto feasible(const State &, const IntegerVariableID &, const Wildcard &) -> bool
    {
        return true;
    }

    auto feasible(const State & state, const IntegerVariableID & var, const IntegerOrWildcard & v) -> bool
    {
        return visit([&](auto & v) { return feasible(state, var, v); }, v);
    }

    auto match(const Integer & a, const Integer & b) -> bool
    {
        return a == b;
    }

    auto match(const Wildcard &, const Integer &) -> bool
    {
        return true;
    }

    auto match(const IntegerOrWildcard & a, const Integer & b) -> bool
    {
        return visit([&](auto & a) { return match(a, b); }, a);
    }

    template <typename T_>
    auto get_tuple_value(const vector<T_> & t, unsigned tuple_idx, unsigned entry)
    {
        return t[tuple_idx][entry];
    }

    template <typename T_>
    auto get_tuple_value(const ArrayParam<T_> & t, unsigned tuple_idx, unsigned entry)
    {
        return get_tuple_value(*t, tuple_idx, entry);
    }
}

template <typename Hint_>
auto gcs::innards::propagate_extensional(
    const ExtensionalData & table, const State & state, auto & inference, ProofLogger * const logger, const Hint_ & hint) -> PropagatorState
{
    // check whether selectable tuples are still feasible
    visit(
        [&](const auto & tuples) {
            auto none_feasible = true;
            for (auto tuple_idx : state.each_value_mutable(table.selector)) {
                bool is_feasible = true;
                for (unsigned idx = 0; idx < table.vars.size(); ++idx)
                    if (! feasible(state, table.vars[idx], get_tuple_value(tuples, tuple_idx.as_index(), idx))) {
                        is_feasible = false;
                        break;
                    }

                if (is_feasible)
                    none_feasible = false;
                else if (logger && logger->get_assertion_level() != AssertionLevel::Off && state.has_single_value(table.selector))
                    // Last selector val so infeasible -> we need an explicit contradiction at higher assertion levels
                    // since there's no table for the implicit one.
                    inference.contradiction(logger, JustifyUsingRUP{hint}, generic_reason(table.vars));
                else
                    inference.infer(logger, table.selector != Integer(tuple_idx), NoJustificationNeeded{}, NoReason{});
            }
            if (none_feasible && logger && logger->get_assertion_level() != AssertionLevel::Off)
                // selector already empty on entry
                inference.contradiction(logger, JustifyUsingRUP{hint}, generic_reason(table.vars));
        },
        table.tuples);

    // check for supports in selectable tuples
    visit(
        [&](const auto & tuples) {
            for (unsigned idx = 0; idx < table.vars.size(); ++idx) {
                for (auto val : state.each_value_mutable(table.vars[idx])) {
                    bool supported = false;
                    for (auto tuple_idx : state.each_value_immutable(table.selector)) {
                        if (match(get_tuple_value(tuples, tuple_idx.as_index(), idx), val)) {
                            supported = true;
                            break;
                        }
                    }

                    if (! supported) {
                        inference.infer(logger, table.vars[idx] != val, JustifyUsingRUP{hint}, generic_reason(table.vars));
                    }
                }
            }
        },
        table.tuples);

    return PropagatorState::Enable;
}

// One instantiation per (inference tracker, hint) pair actually used: NoHint for
// the unnamed AutoTable presolver, hints::Table for Table, hints::LinearEquality
// for the GAC linear encoding. A new caller with its own hint adds a line here.
#define GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hint)                                                                                                  \
    template auto gcs::innards::propagate_extensional(                                                                                               \
        const ExtensionalData &, const State &, SimpleInferenceTracker &, ProofLogger * const, const hint &) -> PropagatorState;                     \
    template auto gcs::innards::propagate_extensional(                                                                                               \
        const ExtensionalData &, const State &, EagerProofLoggingInferenceTracker &, ProofLogger * const, const hint &) -> PropagatorState;

GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(NoHint)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::Table)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::LinearEquality)
GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL(hints::Multiply)

#undef GCS_INSTANTIATE_PROPAGATE_EXTENSIONAL
