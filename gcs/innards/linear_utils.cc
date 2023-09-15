#include <gcs/exception.hh>
#include <gcs/innards/linear_utils.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <util/enumerate.hh>
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
using std::to_string;
using std::variant;
using std::vector;

auto gcs::innards::tidy_up_linear(const WeightedSum & coeff_vars) -> pair<TidiedUpLinear, Integer>
{
    SumOf<Weighted<SimpleIntegerVariableID>> simplified_sum;
    Integer modifier{0_i};
    for (const auto & [c, v] : coeff_vars.terms)
        overloaded{
            [&, &c = c](const SimpleIntegerVariableID & v) { simplified_sum += c * v; },
            [&, &c = c](const ConstantIntegerVariableID & v) { modifier -= c * v.const_value; },
            [&, &c = c](const ViewOfIntegerVariableID & v) {
                simplified_sum += (v.negate_first ? -c : c) * v.actual_variable;
                modifier -= c * v.then_add;
            }}
            .visit(v);

    sort(simplified_sum.terms.begin(), simplified_sum.terms.end(),
        [](const Weighted<SimpleIntegerVariableID> & a, const Weighted<SimpleIntegerVariableID> & b) {
            return a.variable < b.variable;
        });

    // same variable appears twice? bring in its coefficient, and rewrite future
    // coefficients to be zero
    auto c = simplified_sum.terms.begin();
    while (c != simplified_sum.terms.end()) {
        auto c_next = next(c);
        while (c_next != simplified_sum.terms.end() && c_next->variable == c->variable) {
            c->coefficient += c_next->coefficient;
            c_next->coefficient = 0_i;
            ++c_next;
        }
        c = c_next;
    }

    // remove zero coefficients
    simplified_sum.terms.erase(remove_if(simplified_sum.terms.begin(), simplified_sum.terms.end(),
                                   [](const Weighted<SimpleIntegerVariableID> & cv) {
                                       return cv.coefficient == 0_i;
                                   }),
        simplified_sum.terms.end());

    if (simplified_sum.terms.end() == find_if(simplified_sum.terms.begin(), simplified_sum.terms.end(), [](const Weighted<SimpleIntegerVariableID> & cv) -> bool {
            return cv.coefficient != 1_i;
        })) {
        SumOf<SimpleIntegerVariableID> simple_result;
        for (auto & [_, v] : simplified_sum.terms)
            simple_result.terms.emplace_back(v);
        return pair{simple_result, modifier};
    }
    else if (simplified_sum.terms.end() == find_if(simplified_sum.terms.begin(), simplified_sum.terms.end(), [](const Weighted<SimpleIntegerVariableID> & cv) -> bool {
                 return cv.coefficient != 1_i && cv.coefficient != -1_i;
             })) {
        SumOf<PositiveOrNegative<SimpleIntegerVariableID>> sum_result;
        for (auto & [c, v] : simplified_sum.terms)
            sum_result.terms.push_back(PositiveOrNegative<SimpleIntegerVariableID>{c == 1_i, v});
        return pair{sum_result, modifier};
    }
    else
        return pair{simplified_sum, modifier};
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

    auto get_var(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.variable;
    }

    auto get_var(const Weighted<SimpleIntegerVariableID> & cv) -> SimpleIntegerVariableID
    {
        return cv.variable;
    }

    auto get_var(const SimpleIntegerVariableID & cv) -> SimpleIntegerVariableID
    {
        return cv;
    }

    auto get_coeff(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.positive ? 1_i : -1_i;
    }

    auto get_coeff(const Weighted<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.coefficient;
    }

    auto get_coeff(const SimpleIntegerVariableID &) -> Integer
    {
        return 1_i;
    }

    auto get_coeff_or_bool(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> bool
    {
        return cv.positive;
    }

    auto get_coeff_or_bool(const Weighted<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.coefficient;
    }

    auto get_coeff_or_bool(const SimpleIntegerVariableID &) -> bool
    {
        return true;
    }

    auto propagate_linear_or_sum(const auto & coeff_vars, Integer value, State & state, bool equality,
        const std::optional<ProofLine> & proof_line) -> pair<Inference, PropagatorState>
    {
        vector<pair<Integer, Integer>> bounds;
        bounds.reserve(coeff_vars.terms.size());

        auto justify = [&](const SimpleIntegerVariableID & change_var, Proof & proof,
                           bool second_constraint_for_equality, const string & to_what) -> void {
            proof.emit_proof_comment("justifying integer linear inequality " + debug_string(IntegerVariableID{change_var}) + " " + to_what);

            vector<pair<Integer, variant<ProofLine, string>>> terms_to_sum;
            terms_to_sum.emplace_back(1_i, second_constraint_for_equality ? *proof_line + 1 : *proof_line);

            Integer change_var_coeff = 0_i;
            for (const auto & cv : coeff_vars.terms) {
                if (get_var(cv) == change_var) {
                    change_var_coeff = get_coeff(cv);
                    continue;
                }

                if (proof.has_bit_representation(get_var(cv))) {
                    // the following line of logic is definitely correct until you inevitably
                    // discover otherwise
                    bool upper = (get_coeff(cv) < 0_i) != second_constraint_for_equality;

                    auto proof_line = proof.get_or_emit_pol_term_for_bound_in_bits(state, upper,
                        get_var(cv), upper ? state.upper_bound(get_var(cv)) : state.lower_bound(get_var(cv)));

                    terms_to_sum.emplace_back(abs(get_coeff(cv)), proof_line);
                }
                else {
                    throw UnimplementedException{};
                }
            }

            stringstream step;
            step << "p";
            bool first = true;
            for (auto & c_and_l : terms_to_sum) {
                visit([&](const auto & l) {
                    if (c_and_l.first == 1_i)
                        step << " " << l;
                    else
                        step << " " << l << " " << c_and_l.first << " *";
                },
                    c_and_l.second);
                if (! first)
                    step << " +";
                first = false;
            }
            if (change_var_coeff != 1_i)
                step << " " << abs(change_var_coeff) << " d";
            proof.emit_proof_line(step.str(), ProofLevel::Temporary);
        };

        auto infer = [&](int p, const SimpleIntegerVariableID & var, Integer remainder, const auto coeff, bool second_constraint_for_equality) {
            if constexpr (is_same_v<decltype(coeff), const bool>) {
                if (coeff) {
                    if (bounds[p].second >= (1_i + remainder))
                        return state.infer_less_than(var, 1_i + remainder, JustifyExplicitly{[&](Proof & proof) {
                            justify(var, proof, second_constraint_for_equality, "< " + to_string((1_i + remainder).raw_value));
                        }});
                    else
                        return Inference::NoChange;
                }
                else {
                    if (bounds[p].first < -remainder)
                        return state.infer_greater_than_or_equal(var, -remainder, JustifyExplicitly{[&](Proof & proof) {
                            justify(var, proof, second_constraint_for_equality, ">= " + to_string((-remainder).raw_value));
                        }});
                    else
                        return Inference::NoChange;
                }
            }
            else {
                // lots of conditionals to get the rounding right...
                if (coeff > 0_i && remainder >= 0_i) {
                    if (bounds[p].second >= (1_i + remainder / coeff))
                        return state.infer_less_than(var, 1_i + remainder / coeff, JustifyExplicitly{[&](Proof & proof) {
                            justify(var, proof, second_constraint_for_equality, "< " + to_string((1_i + remainder / coeff).raw_value));
                        }});
                    else
                        return Inference::NoChange;
                }
                else if (coeff > 0_i && remainder < 0_i) {
                    auto div_with_rounding = -((-remainder + coeff - 1_i) / coeff);
                    if (bounds[p].second >= 1_i + div_with_rounding)
                        return state.infer_less_than(var, 1_i + div_with_rounding, JustifyExplicitly{[&](Proof & proof) {
                            justify(var, proof, second_constraint_for_equality, "< " + to_string((1_i + div_with_rounding).raw_value));
                        }});
                    else
                        return Inference::NoChange;
                }
                else if (coeff < 0_i && remainder >= 0_i) {
                    if (bounds[p].first < remainder / coeff)
                        return state.infer_greater_than_or_equal(var, remainder / coeff, JustifyExplicitly{[&](Proof & proof) {
                            justify(var, proof, second_constraint_for_equality, ">= " + to_string((remainder / coeff).raw_value));
                        }});
                    else
                        return Inference::NoChange;
                }
                else if (coeff < 0_i && remainder < 0_i) {
                    auto div_with_rounding = (-remainder + -coeff - 1_i) / -coeff;
                    if (bounds[p].first < div_with_rounding)
                        return state.infer_greater_than_or_equal(var, div_with_rounding, JustifyExplicitly{[&](Proof & proof) {
                            justify(var, proof, second_constraint_for_equality, ">= " + to_string((div_with_rounding).raw_value));
                        }});
                    else
                        return Inference::NoChange;
                }
                else
                    throw UnexpectedException{"uh, trying to divide by zero?"};
            }
        };

        bool changed = false;

        Integer lower_sum{0};
        for (const auto & cv : coeff_vars.terms) {
            const auto & var = get_var(cv);
            bounds.push_back(state.bounds(var));
            if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                lower_sum += bounds.back().first;
            else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                lower_sum += (cv.first ? bounds.back().first : -bounds.back().second);
            else {
                auto coeff = get_coeff(cv);
                lower_sum += (coeff >= 0_i) ? (coeff * bounds.back().first) : (coeff * bounds.back().second);
            }
        }

        for (unsigned p = 0, p_end = coeff_vars.terms.size(); p != p_end; ++p) {
            const auto & cv = coeff_vars.terms[p];

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
            else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>) {
                lower_sum = lower_without_me + (cv.first ? bounds[p].first : -bounds[p].second);
            }
            else {
                lower_sum = lower_without_me + ((get_coeff(cv) >= 0_i) ? (get_coeff(cv) * bounds[p].first) : (get_coeff(cv) * bounds[p].second));
            }
        }

        if (equality) {
            Integer inv_lower_sum{0};
            for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
                if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                    inv_lower_sum += -bounds[idx].second;
                else {
                    auto coeff = get_coeff(cv);
                    inv_lower_sum += (-coeff >= 0_i) ? (-coeff * bounds[idx].first) : (-coeff * bounds[idx].second);
                }
            }

            for (unsigned p = 0, p_end = coeff_vars.terms.size(); p != p_end; ++p) {
                const auto & cv = coeff_vars.terms[p];
                Integer inv_lower_without_me{0_i};
                if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                    inv_lower_without_me = inv_lower_sum + bounds[p].second;
                else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                    inv_lower_without_me = inv_lower_sum + (! cv.first ? -bounds[p].first : bounds[p].second);
                else
                    inv_lower_without_me = inv_lower_sum + ((-get_coeff(cv) >= 0_i) ? (get_coeff(cv) * bounds[p].first) : (get_coeff(cv) * bounds[p].second));

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

auto gcs::innards::propagate_linear(const SumOf<Weighted<SimpleIntegerVariableID>> & coeff_vars, Integer value, State & state, bool equality,
    const std::optional<ProofLine> & proof_line) -> pair<Inference, PropagatorState>
{
    return propagate_linear_or_sum(coeff_vars, value, state, equality, proof_line);
}

auto gcs::innards::propagate_sum(const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & coeff_vars, Integer value, State & state, bool equality,
    const std::optional<ProofLine> & proof_line) -> pair<Inference, PropagatorState>
{
    return propagate_linear_or_sum(coeff_vars, value, state, equality, proof_line);
}

auto gcs::innards::propagate_sum_all_positive(const SumOf<SimpleIntegerVariableID> & coeff_vars, Integer value, State & state, bool equality,
    const std::optional<ProofLine> & proof_line) -> pair<Inference, PropagatorState>
{
    return propagate_linear_or_sum(coeff_vars, value, state, equality, proof_line);
}
