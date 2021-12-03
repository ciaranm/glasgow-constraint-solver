/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/linear.hh>
#include <gcs/state.hh>

#include <algorithm>

using namespace gcs;

using std::pair;
using std::remove_if;
using std::sort;

auto gcs::sanitise_linear(Linear & coeff_vars) -> void
{
    sort(coeff_vars.begin(), coeff_vars.end(), [] (const CoefficientAndVariable & a, const CoefficientAndVariable & b) {
            return a.second < b.second;
            });

    // same variable appears twice? bring in its coefficient, and rewrite future
    // coefficients to be zero
    auto c = coeff_vars.begin();
    while (c != coeff_vars.end()) {
        auto c_next = next(c);
        while (c_next != coeff_vars.end() && c_next->second == c->second) {
            c->first += c_next->first;
            c_next->first = 0_i;
            ++c_next;
        }
        c = c_next;
    }

    // remove zero coefficients
    coeff_vars.erase(remove_if(coeff_vars.begin(), coeff_vars.end(), [] (const CoefficientAndVariable & cv) {
                return cv.first == 0_i;
                }), coeff_vars.end());
}

auto gcs::propagate_linear(const Linear & coeff_vars, Integer value, State & state, bool equality) -> pair<Inference, PropagatorState>
{
    // What's the worst value a variable can take, if every other variable
    // is given its best value?
    bool changed = false;

    Integer lower_sum{ 0 }, inv_lower_sum{ 0 };
    for (auto & [ coeff, var ] : coeff_vars)
        lower_sum += (coeff >= 0_i) ? (coeff * state.lower_bound(var)) : (coeff * state.upper_bound(var));
    if (equality)
    for (auto & [ coeff, var ] : coeff_vars)
        inv_lower_sum += (-coeff >= 0_i) ? (-coeff * state.lower_bound(var)) : (-coeff * state.upper_bound(var));

    for (auto & [ coeff, var ] : coeff_vars) {
        Integer lower_without_me = lower_sum - ((coeff >= 0_i) ? (coeff * state.lower_bound(var)) : (coeff * state.upper_bound(var)));
        Integer remainder = value - lower_without_me;
        switch (coeff >= 0_i ?
                state.infer(var < (1_i + remainder / coeff), JustifyUsingRUP{ }) :
                state.infer(var >= remainder / coeff, JustifyUsingRUP{ })) {
            case Inference::Change:        changed = true; break;
            case Inference::NoChange:      break;
            case Inference::Contradiction: return pair{ Inference::Contradiction, PropagatorState::Enable };
        }
        lower_sum = lower_without_me + ((coeff >= 0_i) ? (coeff * state.lower_bound(var)) : (coeff * state.upper_bound(var)));

        if (equality) {
            Integer inv_lower_without_me = inv_lower_sum - ((-coeff >= 0_i) ? (-coeff * state.lower_bound(var)) : (-coeff * state.upper_bound(var)));
            Integer inv_remainder = -value - inv_lower_without_me;
            switch (-coeff >= 0_i ?
                    state.infer(var < (1_i + inv_remainder / -coeff), JustifyUsingRUP{ }) :
                    state.infer(var >= inv_remainder / -coeff, JustifyUsingRUP{ })) {
                case Inference::Change:        changed = true; break;
                case Inference::NoChange:      break;
                case Inference::Contradiction: return pair{ Inference::Contradiction, PropagatorState::Enable };
            }
            inv_lower_sum = inv_lower_without_me + ((-coeff >= 0_i) ? (-coeff * state.lower_bound(var)) : (-coeff * state.upper_bound(var)));
        }
    }

    return pair{ changed ? Inference::Change : Inference::NoChange, PropagatorState::Enable };
}

