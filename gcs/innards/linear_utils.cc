/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>
#include <gcs/innards/linear_utils.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <cstdlib>
#include <sstream>
#include <type_traits>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::is_same_v;
using std::pair;
using std::remove_if;
using std::sort;
using std::string;
using std::stringstream;
using std::vector;

auto gcs::innards::simplify_linear(const Linear & coeff_vars) -> pair<SimpleLinear, Integer>
{
    SimpleLinear result;
    Integer modifier{0_i};
    for (const auto & [c, v] : coeff_vars)
        overloaded{
            [&, &c = c](const SimpleIntegerVariableID & v) { result.emplace_back(c, v); },
            [&, &c = c](const ConstantIntegerVariableID & v) { modifier -= c * v.const_value; },
            [&, &c = c](const ViewOfIntegerVariableID & v) {
                result.emplace_back(v.negate_first ? -c : c, v.actual_variable);
                modifier -= c * v.then_add;
            }}
            .visit(v);

    sort(result.begin(), result.end(), [](const CoefficientAndSimpleVariable & a, const CoefficientAndSimpleVariable & b) {
        return a.second < b.second;
    });

    // same variable appears twice? bring in its coefficient, and rewrite future
    // coefficients to be zero
    auto c = result.begin();
    while (c != result.end()) {
        auto c_next = next(c);
        while (c_next != result.end() && c_next->second == c->second) {
            c->first += c_next->first;
            c_next->first = 0_i;
            ++c_next;
        }
        c = c_next;
    }

    // remove zero coefficients
    result.erase(remove_if(result.begin(), result.end(), [](const CoefficientAndSimpleVariable & cv) {
        return cv.first == 0_i;
    }),
        result.end());

    return pair{result, modifier};
}

auto gcs::innards::sanitise_linear(const Linear & coeff_vars) -> pair<SanitisedLinear, Integer>
{
    auto [result, modifier] = simplify_linear(coeff_vars);

    if (result.end() == find_if(result.begin(), result.end(), [](const CoefficientAndSimpleVariable & cv) -> bool {
            return cv.first != 1_i;
        })) {
        SimpleIntegerVariableIDs simple_result;
        for (auto & [_, v] : result)
            simple_result.emplace_back(v);
        return pair{simple_result, modifier};
    }
    else if (result.end() == find_if(result.begin(), result.end(), [](const CoefficientAndSimpleVariable & cv) -> bool {
                 return cv.first != 1_i && cv.first != -1_i;
             })) {
        SimpleSum sum_result;
        for (auto & [c, v] : result)
            sum_result.emplace_back(c == 1_i, v);
        return pair{sum_result, modifier};
    }
    else
        return pair{result, modifier};
}

namespace
{
    auto negate(Integer v) -> Integer
    {
        return -v;
    }

    auto negate(bool b) -> bool
    {
        return ! b;
    }

    auto get_var(const pair<bool, SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.second;
    }

    auto get_var(const pair<Integer, SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.second;
    }

    auto get_var(const SimpleIntegerVariableID & cv) -> SimpleIntegerVariableID
    {
        return cv;
    }

    auto get_coeff(const pair<bool, SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.first ? 1_i : -1_i;
    }

    auto get_coeff(const pair<Integer, SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.first;
    }

    auto get_coeff(const SimpleIntegerVariableID &) -> Integer
    {
        return 1_i;
    }

    auto get_coeff_or_bool(const pair<bool, SimpleIntegerVariableID> & cv) -> bool
    {
        return cv.first;
    }

    auto get_coeff_or_bool(const pair<Integer, SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.first;
    }

    auto get_coeff_or_bool(const SimpleIntegerVariableID &) -> bool
    {
        return true;
    }

    auto propagate_linear_or_sum(const auto & coeff_vars, Integer value, State & state, bool equality,
        const std::optional<ProofLine> & proof_line) -> pair<Inference, PropagatorState>
    {
        // What's the worst value a variable can take, if every other variable
        // is given its best value?
        bool changed = false;

        vector<pair<Integer, Integer>> bounds;
        bounds.reserve(coeff_vars.size());

        Integer lower_sum{0}, inv_lower_sum{0};
        for (const auto & cv : coeff_vars) {
            const auto & var = get_var(cv);
            bounds.push_back(state.bounds(var));
            if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>) {
                lower_sum += bounds.back().first;
                inv_lower_sum += -bounds.back().second;
            }
            else {
                auto coeff = get_coeff(cv);
                lower_sum += (coeff >= 0_i) ? (coeff * bounds.back().first) : (coeff * bounds.back().second);
                inv_lower_sum += (-coeff >= 0_i) ? (-coeff * bounds.back().first) : (-coeff * bounds.back().second);
            }
        }

        auto justify = [&](const SimpleIntegerVariableID & change_var, Proof & proof, vector<ProofLine> &,
                           bool second_constraint_for_equality) -> void {
            vector<pair<Integer, ProofLine>> lines_to_sum;
            lines_to_sum.emplace_back(1_i, second_constraint_for_equality ? *proof_line - 1 : *proof_line);

            Integer change_var_coeff = 0_i;
            for (const auto & cv : coeff_vars) {
                if (get_var(cv) == change_var) {
                    change_var_coeff = get_coeff(cv);
                    continue;
                }

                // the following line of logic is definitely correct until you inevitably
                // discover otherwise
                bool upper = (get_coeff(cv) < 0_i) != second_constraint_for_equality;

                auto proof_line = proof.get_or_emit_line_for_bound_in_bits(state, upper, get_var(cv), upper ? state.upper_bound(get_var(cv)) : state.lower_bound(get_var(cv)));

                lines_to_sum.emplace_back(abs(get_coeff(cv)), proof_line);
            }

            stringstream step;
            step << "p";
            bool first = true;
            for (auto & [c, l] : lines_to_sum) {
                step << " " << l << " " << c << " *";
                if (! first)
                    step << " +";
                first = false;
            }
            step << " " << abs(change_var_coeff) << " d";
            proof.emit_proof_line(step.str());
        };

        auto infer = [&](int p, const SimpleIntegerVariableID & var, Integer remainder, const auto coeff, bool second_constraint_for_equality) {
            if constexpr (is_same_v<decltype(coeff), const bool>) {
                if (coeff) {
                    if (bounds[p].second >= (1_i + remainder))
                        return state.infer_less_than(var, 1_i + remainder, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality);
                        }});
                    else
                        return Inference::NoChange;
                }
                else {
                    if (bounds[p].first < -remainder)
                        return state.infer_greater_than_or_equal(var, -remainder, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality);
                        }});
                    else
                        return Inference::NoChange;
                }
            }
            else {
                // lots of conditionals to get the rounding right...
                if (coeff > 0_i && remainder >= 0_i) {
                    if (bounds[p].second >= (1_i + remainder / coeff))
                        return state.infer_less_than(var, 1_i + remainder / coeff, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality);
                        }});
                    else
                        return Inference::NoChange;
                }
                else if (coeff > 0_i && remainder < 0_i) {
                    auto div_with_rounding = -((-remainder + coeff - 1_i) / coeff);
                    if (bounds[p].second >= 1_i + div_with_rounding)
                        return state.infer_less_than(var, 1_i + div_with_rounding, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality);
                        }});
                    else
                        return Inference::NoChange;
                }
                else if (coeff < 0_i && remainder >= 0_i) {
                    if (bounds[p].first < remainder / coeff)
                        return state.infer_greater_than_or_equal(var, remainder / coeff, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality);
                        }});
                    else
                        return Inference::NoChange;
                }
                else if (coeff < 0_i && remainder < 0_i) {
                    auto div_with_rounding = (-remainder + -coeff - 1_i) / -coeff;
                    if (bounds[p].first < div_with_rounding)
                        return state.infer_greater_than_or_equal(var, div_with_rounding, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality);
                        }});
                    else
                        return Inference::NoChange;
                }
                else
                    throw UnexpectedException{"uh, trying to divide by zero?"};
            }
        };

        for (unsigned p = 0, p_end = coeff_vars.size(); p != p_end; ++p) {
            const auto & cv = coeff_vars[p];

            Integer lower_without_me{0_i};
            if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                lower_without_me = lower_sum - bounds[p].first;
            else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                lower_without_me = lower_sum - (cv.first ? bounds[p].first : -bounds[p].second);
            else
                lower_without_me = lower_sum - ((get_coeff(cv) >= 0_i) ? (get_coeff(cv) * bounds[p].first) : (get_coeff(cv) * bounds[p].second));
            Integer remainder = value - lower_without_me;

            switch (infer(p, get_var(cv), remainder, get_coeff_or_bool(cv), false)) {
            case Inference::Change:
                bounds[p] = state.bounds(get_var(cv)); // might be tighter than expected if we had holes
                changed = true;
                break;
            case Inference::NoChange:
                break;
            case Inference::Contradiction:
                return pair{Inference::Contradiction, PropagatorState::Enable};
            }

            if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                lower_sum = lower_without_me + bounds[p].first;
            else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                lower_sum = lower_without_me + (cv.first ? bounds[p].first : -bounds[p].second);
            else
                lower_sum = lower_without_me + ((get_coeff(cv) >= 0_i) ? (get_coeff(cv) * bounds[p].first) : (get_coeff(cv) * bounds[p].second));

            if (equality) {
                Integer inv_lower_without_me{0_i};
                if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                    inv_lower_without_me = inv_lower_sum + bounds[p].second;
                else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                    inv_lower_without_me = inv_lower_sum - (! cv.first ? bounds[p].first : -bounds[p].second);
                else
                    inv_lower_without_me = inv_lower_sum - ((-get_coeff(cv) >= 0_i) ? (-get_coeff(cv) * bounds[p].first) : (-get_coeff(cv) * bounds[p].second));

                Integer inv_remainder = -value - inv_lower_without_me;
                switch (infer(p, get_var(cv), inv_remainder, negate(get_coeff_or_bool(cv)), true)) {
                case Inference::Change:
                    bounds[p] = state.bounds(get_var(cv)); // might be tighter than expected if we had holes
                    changed = true;
                    break;
                case Inference::NoChange:
                    break;
                case Inference::Contradiction:
                    return pair{Inference::Contradiction, PropagatorState::Enable};
                }

                if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                    inv_lower_sum = inv_lower_without_me - bounds[p].second;
                else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                    inv_lower_sum = inv_lower_without_me + (! cv.first ? bounds[p].first : -bounds[p].second);
                else
                    inv_lower_sum = inv_lower_without_me + ((-get_coeff(cv) >= 0_i) ? (-get_coeff(cv) * bounds[p].first) : (-get_coeff(cv) * bounds[p].second));
            }
        }

        return pair{changed ? Inference::Change : Inference::NoChange, PropagatorState::Enable};
    }
}

auto gcs::innards::propagate_linear(const SimpleLinear & coeff_vars, Integer value, State & state, bool equality,
    const std::optional<ProofLine> & proof_line) -> pair<Inference, PropagatorState>
{
    return propagate_linear_or_sum(coeff_vars, value, state, equality, proof_line);
}

auto gcs::innards::propagate_sum(const SimpleSum & coeff_vars, Integer value, State & state, bool equality,
    const std::optional<ProofLine> & proof_line) -> pair<Inference, PropagatorState>
{
    return propagate_linear_or_sum(coeff_vars, value, state, equality, proof_line);
}

auto gcs::innards::propagate_sum_all_positive(const SimpleIntegerVariableIDs & coeff_vars, Integer value, State & state, bool equality,
    const std::optional<ProofLine> & proof_line) -> pair<Inference, PropagatorState>
{
    if (state.maybe_proof() || ! equality)
        return propagate_linear_or_sum(coeff_vars, value, state, equality, proof_line);

    bool changed = false;

    vector<pair<Integer, Integer>> bounds;
    bounds.reserve(coeff_vars.size());

    Integer lower_sum{0}, inv_lower_sum{0};
    for (const auto & cv : coeff_vars) {
        const auto & var = get_var(cv);
        bounds.push_back(state.bounds(var));
        lower_sum += bounds.back().first;
        inv_lower_sum += -bounds.back().second;
    }

    for (unsigned p = 0, p_end = coeff_vars.size(); p != p_end; ++p) {
        const auto & cv = coeff_vars[p];

        Integer lower_without_me = lower_sum - bounds[p].first;
        Integer remainder = value - lower_without_me;
        if (bounds[p].second >= (1_i + remainder)) {
            switch (state.infer_less_than(get_var(cv), 1_i + remainder, NoJustificationNeeded{})) {
            case Inference::Change:
                bounds[p] = state.bounds(get_var(cv)); // might be tighter than expected if we had holes
                changed = true;
                break;
            case Inference::NoChange:
                break;
            case Inference::Contradiction:
                return pair{Inference::Contradiction, PropagatorState::Enable};
            }
        }
        lower_sum = lower_without_me + bounds[p].first;

        Integer inv_lower_without_me = inv_lower_sum + bounds[p].second;
        Integer inv_remainder = -value - inv_lower_without_me;
        if (bounds[p].first < -inv_remainder) {
            switch (state.infer_greater_than_or_equal(get_var(cv), -inv_remainder, NoJustificationNeeded{})) {
            case Inference::Change:
                bounds[p] = state.bounds(get_var(cv)); // might be tighter than expected if we had holes
                changed = true;
                break;
            case Inference::NoChange:
                break;
            case Inference::Contradiction:
                return pair{Inference::Contradiction, PropagatorState::Enable};
            }
        }
        inv_lower_sum = inv_lower_without_me - bounds[p].second;
    }

    return pair{changed ? Inference::Change : Inference::NoChange, PropagatorState::Enable};
}
