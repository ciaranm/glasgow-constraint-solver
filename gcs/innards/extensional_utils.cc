#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>

using std::optional;
using std::pair;
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
    auto get_tuple_value(const std::shared_ptr<const T_> & t, unsigned tuple_idx, unsigned entry)
    {
        return get_tuple_value(*t, tuple_idx, entry);
    }
}

auto gcs::innards::propagate_extensional(const ExtensionalData & table, const State & state, auto & inference) -> PropagatorState
{
    // check whether selectable tuples are still feasible
    visit([&](const auto & tuples) {
        state.for_each_value(table.selector, [&](Integer tuple_idx) {
            bool is_feasible = true;
            for (unsigned idx = 0; idx < table.vars.size(); ++idx)
                if (! feasible(state, table.vars[idx], get_tuple_value(tuples, tuple_idx.raw_value, idx))) {
                    is_feasible = false;
                    break;
                }

            if (! is_feasible)
                inference.infer(table.selector != Integer(tuple_idx), NoJustificationNeeded{}, Reason{});
        });
    },
        table.tuples);

    // check for supports in selectable tuples
    visit([&](const auto & tuples) {
        for (unsigned idx = 0; idx < table.vars.size(); ++idx) {
            state.for_each_value(table.vars[idx], [&](Integer val) {
                bool supported = false;
                state.for_each_value_while(table.selector, [&](Integer tuple_idx) -> bool {
                    if (match(get_tuple_value(tuples, tuple_idx.raw_value, idx), val)) {
                        supported = true;
                        return false;
                    }
                    return true;
                });

                if (! supported)
                    inference.infer(table.vars[idx] != val, JustifyUsingRUP{}, generic_reason(state, table.vars));
            });
        }
    },
        table.tuples);

    return PropagatorState::Enable;
}

template auto gcs::innards::propagate_extensional(const ExtensionalData & table, const State & state, SimpleInferenceTracker & inference) -> PropagatorState;
template auto gcs::innards::propagate_extensional(const ExtensionalData & table, const State & state, LogUsingReasonsInferenceTracker & inference) -> PropagatorState;
template auto gcs::innards::propagate_extensional(const ExtensionalData & table, const State & state, LogUsingGuessesInferenceTracker & inference) -> PropagatorState;
