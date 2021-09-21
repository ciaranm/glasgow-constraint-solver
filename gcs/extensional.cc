/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/extensional.hh>
#include <gcs/state.hh>

#include <util/for_each.hh>

using namespace gcs;

auto gcs::propagate_extensional(const ExtensionalData & table, State & state) -> Inference
{
    bool changed = false, contradiction = false;

    // check whether selectable tuples are still feasible
    for_each_with_index(table.tuples, [&] (const auto & tuple, auto tuple_idx) {
        if ((! contradiction) && state.in_domain(table.selector, Integer(tuple_idx))) {
            bool is_feasible = true;
            for_each_with_index(table.vars, [&] (IntegerVariableID var, auto idx) {
                    if (! state.in_domain(var, tuple[idx]))
                        is_feasible = false;
                    });
            if (! is_feasible) {
                switch (state.infer(table.selector != Integer(tuple_idx), NoJustificationNeeded{ })) {
                    case Inference::NoChange:      break;
                    case Inference::Change:        changed = true; break;
                    case Inference::Contradiction: contradiction = true; break;
                }
            }
        }
    });

    if (contradiction)
        return Inference::Contradiction;

    // check for supports in selectable tuples
    for_each_with_index(table.vars, [&] (IntegerVariableID var, auto idx) {
            state.for_each_value(var, [&] (Integer val) {
                    bool supported = false;
                    for_each_with_index(table.tuples, [&] (const auto & tuple, auto tuple_idx) {
                            if (state.in_domain(table.selector, Integer(tuple_idx)) && tuple[idx] == val)
                                supported = true;
                            });

                    if (! supported) {
                        switch (state.infer(var != val, JustifyUsingRUP{ })) {
                            case Inference::NoChange:      break;
                            case Inference::Change:        changed = true; break;
                            case Inference::Contradiction: contradiction = true; break;
                        }
                    }
                });
        });

    return contradiction ? Inference::Contradiction : changed ? Inference::Change : Inference::NoChange;
}

