/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/detail/linear_utils.hh>
#include <gcs/detail/proof.hh>
#include <gcs/detail/state.hh>
#include <gcs/detail/variable_id_utils.hh>
#include <gcs/exception.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <sstream>
#include <type_traits>
#include <vector>

using namespace gcs;

using std::is_same_v;
using std::llabs;
using std::max;
using std::pair;
using std::remove_if;
using std::sort;
using std::string;
using std::stringstream;
using std::variant;
using std::vector;

auto gcs::sanitise_linear(const Linear & coeff_vars) -> pair<variant<SimpleSum, SimpleLinear>, Integer>
{
    SimpleLinear result;
    Integer modifier{0_i};
    for (const auto & [c, v] : coeff_vars)
        overloaded{
            [&, &c = c](const SimpleIntegerVariableID & v) { result.emplace_back(c, v); },
            [&, &c = c](const ConstantIntegerVariableID & v) { modifier -= c * v.const_value; },
            [&, &c = c](const ViewOfIntegerVariableID & v) { result.emplace_back(c, v.actual_variable); modifier -= c * v.offset; }}
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

    if (result.end() == find_if(result.begin(), result.end(), [](const CoefficientAndSimpleVariable & cv) -> bool {
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
    auto get_coeff(bool b) -> Integer
    {
        return b ? 1_i : -1_i;
    }

    auto get_coeff(Integer v) -> Integer
    {
        return v;
    }

    auto negate(bool b) -> bool
    {
        return ! b;
    }

    auto negate(Integer v) -> Integer
    {
        return -v;
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
        for (const auto & [coeff_raw, var] : coeff_vars) {
            bounds.push_back(state.bounds(var));
            auto coeff = get_coeff(coeff_raw);
            lower_sum += (coeff >= 0_i) ? (coeff * bounds.back().first) : (coeff * bounds.back().second);
            inv_lower_sum += (-coeff >= 0_i) ? (-coeff * bounds.back().first) : (-coeff * bounds.back().second);
        }

        auto justify = [&](const SimpleIntegerVariableID & change_var, Proof & proof, vector<ProofLine> & to_delete,
                           bool second_constraint_for_equality, Literal inf_lit) -> void {
            vector<pair<Integer, ProofLine>> lines_to_sum;
            lines_to_sum.emplace_back(1_i, second_constraint_for_equality ? *proof_line - 1 : *proof_line);

            stringstream comment;
            comment << "justifying linear " << (equality ? (second_constraint_for_equality ? "second equality" : "equality") : "inequality");
            for (const auto & [coeff, var] : coeff_vars)
                comment << " " << coeff << " * " << debug_string(IntegerVariableID{var});
            comment << " <= " << value << " bounds change on " << debug_string(IntegerVariableID{change_var}) << " to infer " << debug_string(inf_lit);
            proof.emit_proof_comment(comment.str());

            Integer change_var_coeff = 0_i;
            for (const auto & [coeff, var] : coeff_vars) {
                if (var == change_var) {
                    change_var_coeff = get_coeff(coeff);
                    continue;
                }

                // the following line of logic is definitely correct until you inevitably
                // discover otherwise
                bool upper = (get_coeff(coeff) < 0_i) != second_constraint_for_equality;

                stringstream step;
                step << "u";
                Integer big_number = 0_i;
                proof.for_each_bit_defining_var(var, [&](Integer bit_coeff, string bit_name) {
                    step << " " << (upper ? -bit_coeff : bit_coeff) << " " << bit_name;
                    big_number += Integer{llabs(bit_coeff.raw_value)};
                });

                big_number += Integer{max(1ll, upper ? llabs(state.upper_bound(var).raw_value) : llabs(state.lower_bound(var).raw_value))};
                step << proof.trail_variables(state, big_number);

                if (upper)
                    step << " >= " << -state.upper_bound(var) << " ";
                else
                    step << " >= " << state.lower_bound(var) << " ";

                step << ";";
                auto proof_line = proof.emit_proof_line(step.str());
                lines_to_sum.emplace_back(Integer{llabs(get_coeff(coeff).raw_value)}, proof_line);
                to_delete.push_back(proof_line);
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
            step << " " << llabs(change_var_coeff.raw_value) << " d";
            proof.emit_proof_line(step.str());
        };

        auto infer = [&](int p, const SimpleIntegerVariableID & var, Integer remainder, const auto coeff, bool second_constraint_for_equality) {
            if constexpr (is_same_v<decltype(coeff), const bool>) {
                if (coeff) {
                    if (bounds[p].second >= (1_i + remainder))
                        return state.infer_less_than(var, 1_i + remainder, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality, var < (1_i + remainder));
                        }});
                    else
                        return Inference::NoChange;
                }
                else {
                    if (bounds[p].first < -remainder)
                        return state.infer_greater_than_or_equal(var, -remainder, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality, var >= -remainder);
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
                            justify(var, proof, to_delete, second_constraint_for_equality, var < (1_i + remainder / coeff));
                        }});
                    else
                        return Inference::NoChange;
                }
                else if (coeff > 0_i && remainder < 0_i) {
                    auto div_with_rounding = -((-remainder + coeff - 1_i) / coeff);
                    if (bounds[p].second >= 1_i + div_with_rounding)
                        return state.infer_less_than(var, 1_i + div_with_rounding, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality, var < 1_i + div_with_rounding);
                        }});
                    else
                        return Inference::NoChange;
                }
                else if (coeff < 0_i && remainder >= 0_i) {
                    if (bounds[p].first < remainder / coeff)
                        return state.infer_greater_than_or_equal(var, remainder / coeff, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality, var >= remainder / coeff);
                        }});
                    else
                        return Inference::NoChange;
                }
                else if (coeff < 0_i && remainder < 0_i) {
                    auto div_with_rounding = (-remainder + -coeff - 1_i) / -coeff;
                    if (bounds[p].first < div_with_rounding)
                        return state.infer_greater_than_or_equal(var, div_with_rounding, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                            justify(var, proof, to_delete, second_constraint_for_equality, var >= div_with_rounding);
                        }});
                    else
                        return Inference::NoChange;
                }
                else
                    throw UnexpectedException{"uh, trying to divide by zero?"};
            }
        };

        for (unsigned p = 0, p_end = coeff_vars.size(); p != p_end; ++p) {
            const auto & [coeff, var] = coeff_vars[p];

            Integer lower_without_me{0_i};
            if constexpr (is_same_v<decltype(coeff), const bool>)
                lower_without_me = lower_sum - (coeff ? bounds[p].first : -bounds[p].second);
            else
                lower_without_me = lower_sum - ((coeff >= 0_i) ? (coeff * bounds[p].first) : (coeff * bounds[p].second));
            Integer remainder = value - lower_without_me;

            switch (infer(p, var, remainder, coeff, false)) {
            case Inference::Change:
                bounds[p] = state.bounds(var); // might be tighter than expected if we had holes
                changed = true;
                break;
            case Inference::NoChange:
                break;
            case Inference::Contradiction:
                return pair{Inference::Contradiction, PropagatorState::Enable};
            }

            if constexpr (is_same_v<decltype(coeff), const bool>)
                lower_sum = lower_without_me + (coeff ? bounds[p].first : -bounds[p].second);
            else
                lower_sum = lower_without_me + ((coeff >= 0_i) ? (coeff * bounds[p].first) : (coeff * bounds[p].second));

            if (equality) {
                Integer inv_lower_without_me{0_i};
                if constexpr (is_same_v<decltype(coeff), const bool>)
                    inv_lower_without_me = inv_lower_sum - (! coeff ? bounds[p].first : -bounds[p].second);
                else
                    inv_lower_without_me = inv_lower_sum - ((-coeff >= 0_i) ? (-coeff * bounds[p].first) : (-coeff * bounds[p].second));

                Integer inv_remainder = -value - inv_lower_without_me;
                switch (infer(p, var, inv_remainder, negate(coeff), true)) {
                case Inference::Change:
                    bounds[p] = state.bounds(var); // might be tighter than expected if we had holes
                    changed = true;
                    break;
                case Inference::NoChange:
                    break;
                case Inference::Contradiction:
                    return pair{Inference::Contradiction, PropagatorState::Enable};
                }

                if constexpr (is_same_v<decltype(coeff), const bool>)
                    inv_lower_sum = inv_lower_without_me + (! coeff ? bounds[p].first : -bounds[p].second);
                else
                    inv_lower_sum = inv_lower_without_me + ((-coeff >= 0_i) ? (-coeff * bounds[p].first) : (-coeff * bounds[p].second));
            }
        }

        return pair{changed ? Inference::Change : Inference::NoChange, PropagatorState::Enable};
    }
}

auto gcs::propagate_linear(const SimpleLinear & coeff_vars, Integer value, State & state, bool equality,
    const std::optional<ProofLine> & proof_line) -> pair<Inference, PropagatorState>
{
    return propagate_linear_or_sum(coeff_vars, value, state, equality, proof_line);
}

auto gcs::propagate_sum(const SimpleSum & coeff_vars, Integer value, State & state, bool equality,
    const std::optional<ProofLine> & proof_line) -> pair<Inference, PropagatorState>
{
    return propagate_linear_or_sum(coeff_vars, value, state, equality, proof_line);
}
