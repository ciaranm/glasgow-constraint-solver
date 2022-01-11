/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/linear.hh>
#include <gcs/state.hh>

#include <algorithm>
#include <vector>

using namespace gcs;

using std::pair;
using std::remove_if;
using std::sort;
using std::vector;

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

    vector<pair<Integer, Integer> > bounds;
    bounds.reserve(coeff_vars.size());

    Integer lower_sum{ 0 }, inv_lower_sum{ 0 };
    for (auto & [ coeff, var ] : coeff_vars) {
        bounds.push_back(state.bounds(var));
        lower_sum += (coeff >= 0_i) ? (coeff * bounds.back().first) : (coeff * bounds.back().second);
        inv_lower_sum += (-coeff >= 0_i) ? (-coeff * bounds.back().first) : (-coeff * bounds.back().second);
    }

    auto infer = [&] (int p, IntegerVariableID var, Integer remainder, Integer coeff) {
        if (coeff >= 0_i) {
            if (bounds[p].second >= (1_i + remainder / coeff))
                return state.infer(var < (1_i + remainder / coeff), JustifyUsingAssertion{ });
            else
                return Inference::NoChange;
        }
        else {
            if (bounds[p].first < remainder / coeff)
                return state.infer(var >= remainder / coeff, JustifyUsingAssertion{ });
            else
                return Inference::NoChange;
        }
    };

    for (unsigned p = 0, p_end = coeff_vars.size() ; p != p_end ; ++p) {
        auto & [ coeff, var ] = coeff_vars[p];
        Integer lower_without_me = lower_sum - ((coeff >= 0_i) ? (coeff * bounds[p].first) : (coeff * bounds[p].second));
        Integer remainder = value - lower_without_me;
        switch (infer(p, var, remainder, coeff)) {
            case Inference::Change:
                bounds[p] = state.bounds(var); // might be tighter than expected if we had holes
                changed = true;
                break;
            case Inference::NoChange:
                break;
            case Inference::Contradiction:
                return pair{ Inference::Contradiction, PropagatorState::Enable };
        }
        lower_sum = lower_without_me + ((coeff >= 0_i) ? (coeff * bounds[p].first) : (coeff * bounds[p].second));

        if (equality) {
            Integer inv_lower_without_me = inv_lower_sum - ((-coeff >= 0_i) ? (-coeff * bounds[p].first) : (-coeff * bounds[p].second));
            Integer inv_remainder = -value - inv_lower_without_me;
            switch (infer(p, var, inv_remainder, -coeff)) {
                case Inference::Change:
                    bounds[p] = state.bounds(var); // might be tighter than expected if we had holes
                    changed = true;
                    break;
                case Inference::NoChange:
                    break;
                case Inference::Contradiction:
                    return pair{ Inference::Contradiction, PropagatorState::Enable };
            }
            inv_lower_sum = inv_lower_without_me + ((-coeff >= 0_i) ? (-coeff * bounds[p].first) : (-coeff * bounds[p].second));
        }
    }

    return pair{ changed ? Inference::Change : Inference::NoChange, PropagatorState::Enable };
}

