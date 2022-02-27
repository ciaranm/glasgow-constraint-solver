/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/detail/extensional.hh>
#include <gcs/detail/state.hh>

using std::pair;

using namespace gcs;
using namespace gcs::detail;

auto gcs::detail::propagate_extensional(const ExtensionalData & table, State & state) -> pair<Inference, PropagatorState>
{
    bool changed = false, contradiction = false;

    // check whether selectable tuples are still feasible
    state.for_each_value_while(table.selector, [&](Integer tuple_idx) -> bool {
        bool is_feasible = true;
        for (unsigned idx = 0; idx < table.vars.size(); ++idx)
            if (! state.in_domain(table.vars[idx], table.tuples[tuple_idx.raw_value][idx])) {
                is_feasible = false;
                break;
            }

        if (! is_feasible) {
            switch (state.infer(table.selector != Integer(tuple_idx), NoJustificationNeeded{})) {
            case Inference::NoChange: break;
            case Inference::Change: changed = true; break;
            case Inference::Contradiction: contradiction = true; break;
            }
        }

        return ! contradiction;
    });

    // check for supports in selectable tuples
    for (unsigned idx = 0; idx < table.vars.size(); ++idx) {
        state.for_each_value_while(table.vars[idx], [&](Integer val) -> bool {
            bool supported = false;
            state.for_each_value_while(table.selector, [&](Integer tuple_idx) -> bool {
                if (table.tuples[tuple_idx.raw_value][idx] == val) {
                    supported = true;
                    return false;
                }
                return true;
            });

            if (! supported) {
                switch (state.infer(table.vars[idx] != val, JustifyUsingRUP{})) {
                case Inference::NoChange: break;
                case Inference::Change: changed = true; break;
                case Inference::Contradiction: contradiction = true; break;
                }
            }

            return ! contradiction;
        });

        if (contradiction)
            return pair{Inference::Contradiction, PropagatorState::Enable};
    }

    return pair{contradiction
            ? Inference::Contradiction
            : changed ? Inference::Change
                      : Inference::NoChange,
        PropagatorState::Enable};
}
