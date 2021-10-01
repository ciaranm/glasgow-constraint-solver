/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/extensional.hh>
#include <gcs/state.hh>

using namespace gcs;

auto gcs::propagate_extensional(const ExtensionalData & table, State & state) -> Inference
{
    bool changed = false, contradiction = false;

    // check whether selectable tuples are still feasible
    for (unsigned tuple_idx = 0 ; tuple_idx < table.tuples.size() ; ++tuple_idx) {
        if (state.in_domain(table.selector, Integer(tuple_idx))) {
            bool is_feasible = true;
            for (unsigned idx = 0 ; idx < table.vars.size() ; ++idx)
                if (! state.in_domain(table.vars[idx], table.tuples[tuple_idx][idx])) {
                    is_feasible = false;
                    break;
                }

            if (! is_feasible) {
                switch (state.infer(table.selector != Integer(tuple_idx), NoJustificationNeeded{ })) {
                    case Inference::NoChange:      break;
                    case Inference::Change:        changed = true; break;
                    case Inference::Contradiction: contradiction = true; break;
                }
            }

            if (contradiction)
                return Inference::Contradiction;
        }
    }

    // check for supports in selectable tuples
    for (unsigned idx = 0 ; idx < table.vars.size() ; ++idx) {
        state.for_each_value(table.vars[idx], [&] (Integer val) {
                bool supported = false;
                for (unsigned tuple_idx = 0 ; tuple_idx < table.tuples.size() ; ++tuple_idx)
                    if (state.in_domain(table.selector, Integer(tuple_idx)) && table.tuples[tuple_idx][idx] == val) {
                        supported = true;
                        break;
                    }

                if (! supported) {
                    switch (state.infer(table.vars[idx] != val, JustifyUsingRUP{ })) {
                        case Inference::NoChange:      break;
                        case Inference::Change:        changed = true; break;
                        case Inference::Contradiction: contradiction = true; break;
                    }
                }
            });

        if (contradiction)
            return Inference::Contradiction;
    }

    return contradiction ? Inference::Contradiction : changed ? Inference::Change : Inference::NoChange;
}

