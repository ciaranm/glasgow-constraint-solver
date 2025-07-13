#include <gcs/constraints/linear/justify.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
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

    auto bounds_reason(
        const auto & coeff_vars,
        const SimpleIntegerVariableID & var, bool invert,
        const optional<DetailedReasonOutlineItem> & add_to_reason) -> ReasonOutline
    {
        DetailedReasonOutline reason;
        for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
            if (get_var(cv) != var) {
                if ((get_coeff(cv) < 0_i) != invert) {
                    reason.emplace_back(LessEqualUpperBound{get_var(cv)});
                }
                else {
                    reason.emplace_back(GreaterEqualLowerBound{get_var(cv)});
                }
            }
        }

        if (add_to_reason)
            reason.emplace_back(*add_to_reason);

        return reason;
    }

    auto infer(auto & inference, ProofLogger * const logger,
        const vector<pair<Integer, Integer>> & bounds, const auto & coeff_vars,
        int p, const SimpleIntegerVariableID & var, Integer remainder, const bool coeff, bool second_constraint_for_equality,
        const optional<ProofLine> & proof_line, const optional<DetailedReasonOutlineItem> & add_to_reason) -> void
    {
        if (coeff) {
            if (bounds[p].second >= (1_i + remainder)) {
                auto justf = [&coeff_vars, bounds, var, second_constraint_for_equality, proof_line](ProofLogger & logger, const ExpandedReason &) {
                    justify_linear_bounds(logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                inference.infer_less_than(logger, var, 1_i + remainder, JustifyExplicitly{justf},
                    bounds_reason(coeff_vars, var, second_constraint_for_equality, add_to_reason));
            }
        }
        else {
            if (bounds[p].first < -remainder) {
                auto justf = [&coeff_vars, bounds, var, second_constraint_for_equality, proof_line](ProofLogger & logger, const ExpandedReason &) {
                    justify_linear_bounds(logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                inference.infer_greater_than_or_equal(logger, var, -remainder, JustifyExplicitly{justf},
                    bounds_reason(coeff_vars, var, second_constraint_for_equality, add_to_reason));
            }
        }
    }

    auto infer(auto & inference, ProofLogger * const logger,
        const vector<pair<Integer, Integer>> & bounds, const auto & coeff_vars,
        int p, const SimpleIntegerVariableID & var, Integer remainder, const Integer coeff, bool second_constraint_for_equality,
        const optional<ProofLine> & proof_line, const optional<DetailedReasonOutlineItem> & add_to_reason) -> void
    {
        // lots of conditionals to get the rounding right...
        if (coeff > 0_i && remainder >= 0_i) {
            if (bounds[p].second >= (1_i + remainder / coeff)) {
                auto justf = [&coeff_vars, bounds, var, second_constraint_for_equality, proof_line](ProofLogger & logger, const ExpandedReason &) {
                    justify_linear_bounds(logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                inference.infer_less_than(logger, var, 1_i + remainder / coeff, JustifyExplicitly{justf},
                    bounds_reason(coeff_vars, var, second_constraint_for_equality, add_to_reason));
            }
        }
        else if (coeff > 0_i && remainder < 0_i) {
            auto div_with_rounding = -((-remainder + coeff - 1_i) / coeff);
            if (bounds[p].second >= 1_i + div_with_rounding) {
                auto justf = [&coeff_vars, bounds, var, second_constraint_for_equality, proof_line](ProofLogger & logger, const ExpandedReason &) {
                    justify_linear_bounds(logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                inference.infer_less_than(logger, var, 1_i + div_with_rounding, JustifyExplicitly{justf},
                    bounds_reason(coeff_vars, var, second_constraint_for_equality, add_to_reason));
            }
        }
        else if (coeff < 0_i && remainder >= 0_i) {
            if (bounds[p].first < remainder / coeff) {
                auto justf = [&coeff_vars, bounds, var, second_constraint_for_equality, proof_line](ProofLogger & logger, const ExpandedReason &) {
                    justify_linear_bounds(logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                inference.infer_greater_than_or_equal(logger, var, remainder / coeff, JustifyExplicitly{justf},
                    bounds_reason(coeff_vars, var, second_constraint_for_equality, add_to_reason));
            }
        }
        else if (coeff < 0_i && remainder < 0_i) {
            auto div_with_rounding = (-remainder + -coeff - 1_i) / -coeff;
            if (bounds[p].first < div_with_rounding) {
                auto justf = [&coeff_vars, bounds, var, second_constraint_for_equality, proof_line](ProofLogger & logger, const ExpandedReason &) {
                    justify_linear_bounds(logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                inference.infer_greater_than_or_equal(logger, var, div_with_rounding, JustifyExplicitly{justf},
                    bounds_reason(coeff_vars, var, second_constraint_for_equality, add_to_reason));
            }
        }
        else
            throw UnexpectedException{"uh, trying to divide by zero?"};
    }
}

auto gcs::innards::propagate_linear(const auto & coeff_vars, Integer value, const State & state,
    auto & inference, ProofLogger * const logger,
    bool equality, const optional<ProofLine> & proof_line, const optional<DetailedReasonOutlineItem> & add_to_reason) -> PropagatorState
{
    vector<pair<Integer, Integer>> bounds;
    bounds.reserve(coeff_vars.terms.size());

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

        infer(inference, logger, bounds, coeff_vars, p, get_var(cv), remainder, get_coeff_or_bool(cv),
            false, proof_line, add_to_reason);
        bounds[p] = state.bounds(get_var(cv)); // might be tighter than expected if we had holes

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

            infer(inference, logger, bounds, coeff_vars, p, get_var(cv), inv_remainder, negate(get_coeff_or_bool(cv)),
                true, proof_line, add_to_reason);
            bounds[p] = state.bounds(get_var(cv)); // might be tighter than expected if we had holes

            if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                inv_lower_sum = inv_lower_without_me - bounds[p].second;
            else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                inv_lower_sum = inv_lower_without_me + (! cv.first ? bounds[p].first : -bounds[p].second);
            else
                inv_lower_sum = inv_lower_without_me + ((-get_coeff(cv) >= 0_i) ? (-get_coeff(cv) * bounds[p].first) : (-get_coeff(cv) * bounds[p].second));
        }
    }

    return PropagatorState::Enable;
}

template auto gcs::innards::propagate_linear(const SumOf<Weighted<SimpleIntegerVariableID>> & coeff_vars,
    Integer value, const State & state, SimpleInferenceTracker &, ProofLogger * const logger,
    bool equality, const optional<ProofLine> & proof_line, const optional<DetailedReasonOutlineItem> & add_to_reason) -> PropagatorState;

template auto gcs::innards::propagate_linear(const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & coeff_vars,
    Integer value, const State & state, SimpleInferenceTracker &, ProofLogger * const logger,
    bool equality, const optional<ProofLine> & proof_line, const optional<DetailedReasonOutlineItem> & add_to_reason) -> PropagatorState;

template auto gcs::innards::propagate_linear(const SumOf<SimpleIntegerVariableID> & coeff_vars,
    Integer value, const State & state, SimpleInferenceTracker &, ProofLogger * const logger,
    bool equality, const optional<ProofLine> & proof_line, const optional<DetailedReasonOutlineItem> & add_to_reason) -> PropagatorState;

template auto gcs::innards::propagate_linear(const SumOf<Weighted<SimpleIntegerVariableID>> & coeff_vars,
    Integer value, const State & state, EagerProofLoggingInferenceTracker &, ProofLogger * const logger,
    bool equality, const optional<ProofLine> & proof_line, const optional<DetailedReasonOutlineItem> & add_to_reason) -> PropagatorState;

template auto gcs::innards::propagate_linear(const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & coeff_vars,
    Integer value, const State & state, EagerProofLoggingInferenceTracker &, ProofLogger * const logger,
    bool equality, const optional<ProofLine> & proof_line, const optional<DetailedReasonOutlineItem> & add_to_reason) -> PropagatorState;

template auto gcs::innards::propagate_linear(const SumOf<SimpleIntegerVariableID> & coeff_vars,
    Integer value, const State & state, EagerProofLoggingInferenceTracker &, ProofLogger * const logger,
    bool equality, const optional<ProofLine> & proof_line, const optional<DetailedReasonOutlineItem> & add_to_reason) -> PropagatorState;

auto gcs::innards::propagate_linear_not_equals(const auto & coeff_vars, Integer value, const State & state,
    auto & inference, ProofLogger * const logger) -> PropagatorState
{
    // condition is definitely false, so this is inequality. so long as at least two variables aren't
    // fixed, don't try to do anything.
    auto single_unset = coeff_vars.terms.end();
    Integer accum = 0_i;
    for (auto i = coeff_vars.terms.begin(), i_end = coeff_vars.terms.end(); i != i_end; ++i) {
        auto val = state.optional_single_value(get_var(*i));
        if (val)
            accum += get_coeff(*i) * *val;
        else {
            if (single_unset != coeff_vars.terms.end()) {
                // we've found at least two unset variables, do nothing for now
                return PropagatorState::Enable;
            }
            else
                single_unset = i;
        }
    }

    if (single_unset == coeff_vars.terms.end()) {
        // every variable is set, do a sanity check
        if (accum == value) {
            // we've set every variable and have equality
            inference.contradiction(logger, JustifyUsingRUP{}, AllVariablesExactValues{});
        }
        else
            return PropagatorState::DisableUntilBacktrack;
    }
    else {
        // exactly one thing remaining, so it can't be given the single value that would
        // make the equality hold.
        Integer residual = value - accum;
        if (0_i == residual % get_coeff(*single_unset)) {
            Integer forbidden = residual / get_coeff(*single_unset);
            if (state.in_domain(get_var(*single_unset), forbidden)) {
                // the forbidden value is in the domain, so disallow it, and then
                // we won't do anything else.
                inference.infer(logger, get_var(*single_unset) != forbidden,
                    JustifyUsingRUP{}, AllVariablesExactValues{});
                return PropagatorState::DisableUntilBacktrack;
            }
            else {
                // the forbidden value isn't in the domain, we're not going to do
                // anything else
                return PropagatorState::DisableUntilBacktrack;
            }
        }
        else {
            // the forbidden value isn't an integer, so it can't happen
            return PropagatorState::DisableUntilBacktrack;
        }
    }
}

template auto gcs::innards::propagate_linear_not_equals(const SumOf<Weighted<SimpleIntegerVariableID>> & terms, Integer,
    const State &, SimpleInferenceTracker &, ProofLogger * const logger) -> PropagatorState;

template auto gcs::innards::propagate_linear_not_equals(const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & terms, Integer,
    const State &, SimpleInferenceTracker &, ProofLogger * const logger) -> PropagatorState;

template auto gcs::innards::propagate_linear_not_equals(const SumOf<SimpleIntegerVariableID> & terms, Integer,
    const State &, SimpleInferenceTracker &, ProofLogger * const logger) -> PropagatorState;

template auto gcs::innards::propagate_linear_not_equals(const SumOf<Weighted<SimpleIntegerVariableID>> & terms, Integer,
    const State &, EagerProofLoggingInferenceTracker &, ProofLogger * const logger) -> PropagatorState;

template auto gcs::innards::propagate_linear_not_equals(const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & terms, Integer,
    const State &, EagerProofLoggingInferenceTracker &, ProofLogger * const logger) -> PropagatorState;

template auto gcs::innards::propagate_linear_not_equals(const SumOf<SimpleIntegerVariableID> & terms, Integer,
    const State &, EagerProofLoggingInferenceTracker &, ProofLogger * const logger) -> PropagatorState;
