#include <gcs/constraints/knapsack.hh>
#include <gcs/exception.hh>
#include <gcs/innards/opb_utils.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <map>
#include <optional>
#include <sstream>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::map;
using std::max;
using std::move;
using std::optional;
using std::pair;
using std::size_t;
using std::string;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::vector;

Knapsack::Knapsack(vector<Integer> weights, vector<Integer> profits,
    vector<IntegerVariableID> vars, IntegerVariableID weight, IntegerVariableID profit) :
    _weights(move(weights)),
    _profits(move(profits)),
    _vars(move(vars)),
    _weight(weight),
    _profit(profit)
{
}

auto Knapsack::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Knapsack>(_weights, _profits, _vars, _weight, _profit);
}

namespace
{
    auto knapsack_best_profit_recursive(
        vector<map<Integer, Integer>> & dp_table,
        const vector<Integer> & weights, const vector<Integer> & profits,
        const vector<size_t> & undetermined_vars, size_t idx, Integer remaining_weight) -> Integer
    {
        if (idx >= undetermined_vars.size())
            return 0_i;

        auto iter = dp_table.at(idx).find(remaining_weight);
        if (iter != dp_table.at(idx).end())
            return iter->second;

        Integer result_no_take = knapsack_best_profit_recursive(dp_table, weights, profits, undetermined_vars, idx + 1, remaining_weight);
        optional<Integer> result_take;
        if (remaining_weight >= weights[undetermined_vars[idx]])
            result_take = knapsack_best_profit_recursive(dp_table, weights, profits, undetermined_vars, idx + 1,
                              remaining_weight - weights[undetermined_vars[idx]]) +
                profits[undetermined_vars[idx]];

        Integer result = (! result_take) ? result_no_take : max(*result_take, result_no_take);
        dp_table.at(idx).emplace(remaining_weight, result);
        return result;
    }

    auto knapsack_best_profit_bottom(
        const vector<Integer> & weights, const vector<Integer> & profits,
        const vector<IntegerVariableID> &,
        const vector<size_t> & undetermined_vars, Integer remaining_weight) -> Integer
    {
        map<Integer, Integer> options;
        options.emplace(0_i, 0_i);

        for (const auto & [idx_pos, idx] : enumerate(undetermined_vars)) {
            map<Integer, Integer> new_options;
            for (auto & [weight, profit] : options) {
                auto no_take = new_options.try_emplace(weight, profit).first;
                no_take->second = max(no_take->second, profit);
                if (weight + weights.at(idx) <= remaining_weight) {
                    auto take = new_options.try_emplace(weight + weights.at(idx), profit + profits.at(idx)).first;
                    take->second = max(take->second, profit + profits.at(idx));
                }
            }

            options = move(new_options);
        }

        return max_element(options.begin(), options.end(), [&](const auto & a, const auto & b) { return a.second < b.second; })->second;
    }

    auto knapsack(State & state, const vector<Integer> & weights, const vector<Integer> & profits,
        const vector<IntegerVariableID> & vars, IntegerVariableID weight, IntegerVariableID profit) -> pair<Inference, PropagatorState>
    {
        vector<size_t> undetermined_vars;
        Integer used_weight = 0_i, accumulated_profit = 0_i;
        for (const auto & [idx, v] : enumerate(vars)) {
            auto val = state.optional_single_value(v);
            if (! val)
                undetermined_vars.push_back(idx);
            else if (1_i == *val) {
                used_weight += weights[idx];
                accumulated_profit += profits[idx];
            }
            else if (0_i != *val)
                throw UnexpectedException{"can only support 0-1 variables for knapsack"};
        }

        if (undetermined_vars.empty()) {
            auto inference = state.infer(weight == used_weight, NoJustificationNeeded{});
            if (inference != Inference::Contradiction)
                increase_inference_to(inference, state.infer(profit == accumulated_profit, NoJustificationNeeded{}));
            return pair{inference, PropagatorState::DisableUntilBacktrack};
        }

        auto inference = state.infer(profit >= accumulated_profit, NoJustificationNeeded{});
        if (Inference::Contradiction == inference)
            return pair{inference, PropagatorState::Enable};

        inference = state.infer(weight >= used_weight, NoJustificationNeeded{});
        if (Inference::Contradiction == inference)
            return pair{inference, PropagatorState::Enable};

        optional<vector<pair<bool, string>>> proof_lines;
        if (state.maybe_proof())
            proof_lines.emplace();

        vector<map<Integer, Integer>> dp_table{undetermined_vars.size() + 1};
        auto best_profit_recursive = knapsack_best_profit_recursive(dp_table, weights, profits, undetermined_vars,
                                         0, state.upper_bound(weight) - used_weight) +
            accumulated_profit;

        auto best_profit_bottom = knapsack_best_profit_bottom(weights, profits, vars, undetermined_vars,
                                      state.upper_bound(weight - used_weight)) +
            accumulated_profit;

        if (best_profit_recursive != best_profit_bottom)
            throw UnexpectedException{"profits mismatch, " + to_string(best_profit_recursive.raw_value) + " / " +
                to_string(best_profit_bottom.raw_value)};

        return pair{state.infer(profit < 1_i + best_profit_recursive, JustifyUsingAssertion{}), PropagatorState::Enable};
    }
}

auto Knapsack::install(Propagators & propagators, State & initial_state) && -> void
{
    if (_weights.size() != _profits.size() || _weights.size() != _vars.size())
        throw UnexpectedException{"not sure what to do about different array sizes for knapsack"};

    for (auto & w : _weights)
        if (w < 0_i)
            throw UnexpectedException{"not sure what to do about negative weights for knapsack"};

    for (auto & p : _profits)
        if (p < 0_i)
            throw UnexpectedException{"not sure what to do about negative profits for knapsack"};

    if (initial_state.lower_bound(_weight) < 0_i)
        throw UnexpectedException{"not sure what to do about negative permitted weight for knapsack"};

    if (initial_state.lower_bound(_profit) < 0_i)
        throw UnexpectedException{"not sure what to do about negative permitted profit for knapsack"};

    for (auto & v : _vars)
        if (initial_state.bounds(v) != pair{0_i, 1_i})
            throw UnexpectedException{"can only support 0-1 variables for knapsack"};

    if (propagators.want_definitions()) {
        WeightedPseudoBooleanSum weights_eq, profits_eq;
        for (const auto & [idx, v] : enumerate(_vars)) {
            weights_eq += _weights[idx] * v;
            profits_eq += _profits[idx] * v;
        }
        propagators.define(initial_state, weights_eq == 1_i * _weight);
        propagators.define(initial_state, profits_eq == 1_i * _profit);
    }

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};
    triggers.on_change.emplace_back(_weight);
    triggers.on_change.emplace_back(_profit);

    propagators.install(
        [weights = move(_weights), profits = move(_profits), vars = move(_vars), weight = move(_weight), profit = move(_profit)](State & state) -> pair<Inference, PropagatorState> {
            return knapsack(state, weights, profits, vars, weight, profit);
        },
        triggers, "knapsack");
}

auto Knapsack::describe_for_proof() -> std::string
{
    return "knapsack";
}
