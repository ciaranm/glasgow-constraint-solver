#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <util/enumerate.hh>

#include <sstream>
#include <string>
#include <type_traits>

using std::is_same_v;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::to_string;
using std::variant;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

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

    auto bounds_reason(State & state, const auto & coeff_vars, const SimpleIntegerVariableID & var, bool invert,
        const optional<Literal> & add_to_reason) -> Reason
    {
        Reason reason;
        for (const auto & cv : coeff_vars.terms) {
            if (get_var(cv) != var) {
                if ((get_coeff(cv) < 0_i) != invert) {
                    reason.emplace_back(get_var(cv) < state.upper_bound(get_var(cv)) + 1_i);
                }
                else {
                    reason.emplace_back(get_var(cv) >= state.lower_bound(get_var(cv)));
                }
            }
        }

        if (add_to_reason) {
            overloaded{
                [&](const TrueLiteral &) {},
                [&](const FalseLiteral &) {},
                [&](const IntegerVariableCondition & cond) {
                    switch (cond.op) {
                    case VariableConditionOperator::NotEqual:
                        reason.emplace_back(cond.var != cond.value);
                        break;
                    case VariableConditionOperator::Equal:
                        reason.emplace_back(cond.var == cond.value);
                        break;
                    case VariableConditionOperator::Less:
                        reason.emplace_back(cond.var < cond.value);
                        break;
                    case VariableConditionOperator::GreaterEqual:
                        reason.emplace_back(cond.var >= cond.value);
                        break;
                    }
                }}
                .visit(*add_to_reason);
        }

        return reason;
    }

    auto justify_bounds(State & state, const auto & coeff_vars, const SimpleIntegerVariableID & change_var, ProofLogger & logger,
        bool second_constraint_for_equality, const string & to_what, const ProofLine proof_line) -> void
    {
        logger.emit_proof_comment("justifying integer linear inequality " + debug_string(IntegerVariableID{change_var}) + " " + to_what);

        vector<pair<Integer, variant<ProofLine, string>>> terms_to_sum;
        terms_to_sum.emplace_back(1_i, second_constraint_for_equality ? proof_line + 1 : proof_line);

        Integer change_var_coeff = 0_i;
        for (const auto & cv : coeff_vars.terms) {
            if (get_var(cv) == change_var) {
                change_var_coeff = get_coeff(cv);
                continue;
            }

            // the following line of logic is definitely correct until you inevitably
            // discover otherwise
            bool upper = (get_coeff(cv) < 0_i) != second_constraint_for_equality;

            auto literal_defining_proof_line = logger.variable_constraints_tracker().need_pol_item_defining_literal(
                upper ? get_var(cv) < state.upper_bound(get_var(cv) + 1_i) : get_var(cv) >= state.lower_bound(get_var(cv)));

            terms_to_sum.emplace_back(abs(get_coeff(cv)), literal_defining_proof_line);
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
        logger.emit_proof_line(step.str(), ProofLevel::Temporary);
    }

    auto infer(State & state, ProofLogger * const logger, const vector<pair<Integer, Integer>> & bounds, const auto & coeff_vars,
        int p, const SimpleIntegerVariableID & var, Integer remainder, const bool coeff, bool second_constraint_for_equality,
        const optional<ProofLine> & proof_line, const optional<Literal> & add_to_reason)
    {
        if (coeff) {
            if (bounds[p].second >= (1_i + remainder)) {
                auto justf = [&]() {
                    justify_bounds(state, coeff_vars, var, *logger, second_constraint_for_equality,
                        "< " + to_string((1_i + remainder).raw_value), *proof_line);
                };
                auto just = JustifyExplicitly{justf, bounds_reason(state, coeff_vars, var, second_constraint_for_equality, add_to_reason)};
                return state.infer_less_than(logger, var, 1_i + remainder, just);
            }
            else
                return Inference::NoChange;
        }
        else {
            if (bounds[p].first < -remainder) {
                auto justf = [&]() {
                    justify_bounds(state, coeff_vars, var, *logger, second_constraint_for_equality,
                        ">= " + to_string((-remainder).raw_value), *proof_line);
                };
                auto just = JustifyExplicitly{justf, bounds_reason(state, coeff_vars, var, second_constraint_for_equality, add_to_reason)};
                return state.infer_greater_than_or_equal(logger, var, -remainder, just);
            }
            else
                return Inference::NoChange;
        }
    }

    auto infer(State & state, ProofLogger * const logger, const vector<pair<Integer, Integer>> & bounds, const auto & coeff_vars,
        int p, const SimpleIntegerVariableID & var, Integer remainder, const Integer coeff, bool second_constraint_for_equality,
        const optional<ProofLine> & proof_line, const optional<Literal> & add_to_reason)
    {
        // lots of conditionals to get the rounding right...
        if (coeff > 0_i && remainder >= 0_i) {
            if (bounds[p].second >= (1_i + remainder / coeff)) {
                auto justf = [&]() {
                    justify_bounds(state, coeff_vars, var, *logger, second_constraint_for_equality,
                        "< " + to_string((1_i + remainder / coeff).raw_value), *proof_line);
                };
                auto just = JustifyExplicitly{justf, bounds_reason(state, coeff_vars, var, second_constraint_for_equality, add_to_reason)};
                return state.infer_less_than(logger, var, 1_i + remainder / coeff, just);
            }
            else
                return Inference::NoChange;
        }
        else if (coeff > 0_i && remainder < 0_i) {
            auto div_with_rounding = -((-remainder + coeff - 1_i) / coeff);
            if (bounds[p].second >= 1_i + div_with_rounding) {
                auto justf = [&]() {
                    justify_bounds(state, coeff_vars, var, *logger, second_constraint_for_equality,
                        "< " + to_string((1_i + div_with_rounding).raw_value), *proof_line);
                };
                auto just = JustifyExplicitly{justf, bounds_reason(state, coeff_vars, var, second_constraint_for_equality, add_to_reason)};
                return state.infer_less_than(logger, var, 1_i + div_with_rounding, just);
            }
            else
                return Inference::NoChange;
        }
        else if (coeff < 0_i && remainder >= 0_i) {
            if (bounds[p].first < remainder / coeff) {
                auto justf = [&]() {
                    justify_bounds(state, coeff_vars, var, *logger, second_constraint_for_equality,
                        ">= " + to_string((remainder / coeff).raw_value), *proof_line);
                };
                auto just = JustifyExplicitly{justf, bounds_reason(state, coeff_vars, var, second_constraint_for_equality, add_to_reason)};
                return state.infer_greater_than_or_equal(logger, var, remainder / coeff, just);
            }
            else
                return Inference::NoChange;
        }
        else if (coeff < 0_i && remainder < 0_i) {
            auto div_with_rounding = (-remainder + -coeff - 1_i) / -coeff;
            if (bounds[p].first < div_with_rounding) {
                auto justf = [&]() {
                    justify_bounds(state, coeff_vars, var, *logger, second_constraint_for_equality,
                        ">= " + to_string((div_with_rounding).raw_value), *proof_line);
                };
                auto just = JustifyExplicitly{justf, bounds_reason(state, coeff_vars, var, second_constraint_for_equality, add_to_reason)};
                return state.infer_greater_than_or_equal(logger, var, div_with_rounding, just);
            }
            else
                return Inference::NoChange;
        }
        else
            throw UnexpectedException{"uh, trying to divide by zero?"};
    }

    auto propagate_linear_or_sum(const auto & coeff_vars, Integer value, State & state, ProofLogger * const logger,
        bool equality, const optional<ProofLine> & proof_line, const optional<Literal> & add_to_reason) -> pair<Inference, PropagatorState>
    {
        vector<pair<Integer, Integer>> bounds;
        bounds.reserve(coeff_vars.terms.size());

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

            switch (infer(state, logger, bounds, coeff_vars, p, get_var(cv), remainder, get_coeff_or_bool(cv),
                false, proof_line, add_to_reason)) {
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

                switch (infer(state, logger, bounds, coeff_vars, p, get_var(cv), inv_remainder, negate(get_coeff_or_bool(cv)),
                    true, proof_line, add_to_reason)) {
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

auto gcs::innards::propagate_linear(const SumOf<Weighted<SimpleIntegerVariableID>> & coeff_vars, Integer value,
    State & state, ProofLogger * const logger, bool equality,
    const optional<ProofLine> & proof_line,
    const optional<Literal> & add_to_reason) -> pair<Inference, PropagatorState>
{
    return propagate_linear_or_sum(coeff_vars, value, state, logger, equality, proof_line, add_to_reason);
}

auto gcs::innards::propagate_sum(const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & coeff_vars, Integer value,
    State & state, ProofLogger * const logger, bool equality,
    const optional<ProofLine> & proof_line,
    const optional<Literal> & add_to_reason) -> pair<Inference, PropagatorState>
{
    return propagate_linear_or_sum(coeff_vars, value, state, logger, equality, proof_line, add_to_reason);
}

auto gcs::innards::propagate_sum_all_positive(const SumOf<SimpleIntegerVariableID> & coeff_vars, Integer value,
    State & state, ProofLogger * const logger, bool equality,
    const optional<ProofLine> & proof_line,
    const optional<Literal> & add_to_reason) -> pair<Inference, PropagatorState>
{
    return propagate_linear_or_sum(coeff_vars, value, state, logger, equality, proof_line, add_to_reason);
}
