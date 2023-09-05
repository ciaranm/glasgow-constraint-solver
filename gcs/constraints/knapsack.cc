#include <gcs/constraints/knapsack.hh>
#include <gcs/exception.hh>
#include <gcs/innards/opb_utils.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <map>
#include <optional>
#include <sstream>
#include <tuple>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::map;
using std::max;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
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

        auto remaining_weight = state.upper_bound(weight - used_weight);
        auto best_profit_bottom = knapsack_best_profit_bottom(weights, profits, vars, undetermined_vars, remaining_weight) + accumulated_profit;

        return pair{state.infer(profit < 1_i + best_profit_bottom, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                        auto trail = proof.trail_variables_as_sum(state, 1_i);

                        map<Integer, tuple<Integer, optional<ProofFlag>, optional<ProofFlag>, optional<ProofFlag>, optional<ProofLine>, optional<ProofLine>>> options;
                        options.emplace(0_i, tuple{0_i, nullopt, nullopt, nullopt, nullopt, nullopt});

                        for (const auto & [idx_pos, idx] : enumerate(undetermined_vars)) {
                            map<Integer, tuple<Integer, optional<ProofFlag>, optional<ProofFlag>, optional<ProofFlag>, optional<ProofLine>, optional<ProofLine>>> new_options;
                            vector<ProofFlag> options_at_current_level;
                            for (const auto & [option_idx, option] : enumerate(options)) {
                                const auto & [weight, profit_and_flag] = option;
                                const auto & [profit, current_option_weight, current_option_profit, current_option_both, current_option_weight_line, current_option_profit_line] = profit_and_flag;

                                WeightedPseudoBooleanSum sum_of_weights_so_far, sum_of_profits_so_far;
                                for (const auto & [accum_idx_pos, accum_idx] : enumerate(undetermined_vars)) {
                                    sum_of_weights_so_far += weights.at(accum_idx) * vars.at(accum_idx);
                                    sum_of_profits_so_far += profits.at(accum_idx) * vars.at(accum_idx);
                                    if (accum_idx_pos == idx_pos)
                                        break;
                                }

                                auto no_take_lhs_weight = trail, no_take_lhs_profit = trail, no_take_lhs_both = trail;
                                if (current_option_weight)
                                    no_take_lhs_weight += 1_i * ! *current_option_weight;
                                if (current_option_profit)
                                    no_take_lhs_profit += 1_i * ! *current_option_profit;
                                if (current_option_both)
                                    no_take_lhs_both += 1_i * ! *current_option_both;
                                no_take_lhs_weight += 1_i * (vars.at(idx_pos) != 0_i);
                                no_take_lhs_profit += 1_i * (vars.at(idx_pos) != 0_i);
                                no_take_lhs_both += 1_i * (vars.at(idx_pos) != 0_i);

                                proof.emit_proof_comment("*** no take option " + to_string(idx_pos) + "." + to_string(option_idx));
                                proof.emit_proof_comment("define no take >= weight " + to_string(idx_pos) + "." + to_string(option_idx));
                                auto [no_take_sum_weights_ge_weight, no_take_weight_line, _1] = proof.create_proof_flag_reifying(
                                    sum_of_weights_so_far >= weight,
                                    "option_" + to_string(option_idx) + "_no_take_sum_" + to_string(idx_pos) + "_weights_ge_" + to_string(weight.raw_value));
                                if (current_option_weight_line)
                                    proof.emit_proof_line("p -1 " + to_string(*current_option_weight_line) + " +");
                                proof.emit_rup_proof_line(no_take_lhs_weight + 1_i * no_take_sum_weights_ge_weight >= 1_i);
                                proof.emit_rup_proof_line(no_take_lhs_both + 1_i * no_take_sum_weights_ge_weight >= 1_i);

                                proof.emit_proof_comment("define no take <= profit " + to_string(idx_pos) + "." + to_string(option_idx));
                                auto [no_take_sum_profits_le_profit, no_take_profit_line, _2] = proof.create_proof_flag_reifying(
                                    sum_of_profits_so_far <= profit,
                                    "option_" + to_string(option_idx) + "_no_take_sum_" + to_string(idx_pos) + "_profits_le_" + to_string(profit.raw_value));
                                if (current_option_profit_line)
                                    proof.emit_proof_line("p -1 " + to_string(*current_option_profit_line) + " +");
                                proof.emit_rup_proof_line(no_take_lhs_profit + 1_i * no_take_sum_profits_le_profit >= 1_i);
                                proof.emit_rup_proof_line(no_take_lhs_both + 1_i * no_take_sum_profits_le_profit >= 1_i);

                                proof.emit_proof_comment("define no take both " + to_string(idx_pos) + "." + to_string(option_idx));
                                auto [no_take_both_sums, _3, _4] = proof.create_proof_flag_reifying(
                                    WeightedPseudoBooleanSum{} + 1_i * no_take_sum_weights_ge_weight + 1_i * no_take_sum_profits_le_profit >= 2_i,
                                    "option_" + to_string(option_idx) + "_no_take_both_sums_" + to_string(idx_pos) + "_" + to_string(weight.raw_value) + "_" + to_string(profit.raw_value));
                                proof.emit_rup_proof_line(no_take_lhs_both + 1_i * no_take_both_sums >= 1_i);

                                auto no_take = new_options.try_emplace(weight, tuple{profit, no_take_sum_weights_ge_weight, no_take_sum_profits_le_profit, no_take_both_sums, no_take_weight_line, no_take_profit_line}).first;
                                get<0>(no_take->second) = max(get<0>(no_take->second), profit);
                                if (get<0>(no_take->second) != profit)
                                    proof.emit_proof_comment("!!! found better profit 1");

                                optional<ProofFlag> take_weight_sum_if_permitted, take_profit_sum_if_permitted, take_both_sums_if_permitted;
                                if (weight + weights.at(idx) <= remaining_weight) {
                                    auto take_lhs_weight = trail, take_lhs_profit = trail, take_lhs_both = trail;
                                    if (current_option_weight)
                                        take_lhs_weight += 1_i * ! *current_option_weight;
                                    if (current_option_profit)
                                        take_lhs_profit += 1_i * ! *current_option_profit;
                                    if (current_option_both)
                                        take_lhs_both += 1_i * ! *current_option_both;
                                    take_lhs_weight += 1_i * (vars.at(idx_pos) != 1_i);
                                    take_lhs_profit += 1_i * (vars.at(idx_pos) != 1_i);
                                    take_lhs_both += 1_i * (vars.at(idx_pos) != 1_i);

                                    auto take_weight = weight + weights.at(idx);
                                    auto take_profit = profit + profits.at(idx);

                                    proof.emit_proof_comment("*** take option " + to_string(idx_pos) + "." + to_string(option_idx));
                                    proof.emit_proof_comment("define take >= weight " + to_string(idx_pos) + "." + to_string(option_idx));
                                    auto [take_sum_weights_ge_weight, take_weight_line, _1] = proof.create_proof_flag_reifying(
                                        sum_of_weights_so_far >= take_weight,
                                        "option_" + to_string(option_idx) + "_take_sum_" + to_string(idx_pos) + "_weights_ge_" + to_string(take_weight.raw_value));
                                    if (current_option_weight_line)
                                        proof.emit_proof_line("p -1 " + to_string(*current_option_weight_line) + " +");
                                    proof.emit_rup_proof_line(take_lhs_weight + 1_i * take_sum_weights_ge_weight >= 1_i);
                                    proof.emit_rup_proof_line(take_lhs_both + 1_i * take_sum_weights_ge_weight >= 1_i);

                                    proof.emit_proof_comment("define take <= profit " + to_string(idx_pos) + "." + to_string(option_idx));
                                    auto [take_sum_profits_le_profit, take_profit_line, _2] = proof.create_proof_flag_reifying(
                                        sum_of_profits_so_far <= take_profit,
                                        "option_" + to_string(option_idx) + "_take_sum_" + to_string(idx_pos) + "_profits_le_" + to_string(take_profit.raw_value));
                                    if (current_option_profit_line)
                                        proof.emit_proof_line("p -1 " + to_string(*current_option_profit_line) + " +");
                                    proof.emit_rup_proof_line(take_lhs_profit + 1_i * take_sum_profits_le_profit >= 1_i);
                                    proof.emit_rup_proof_line(take_lhs_both + 1_i * take_sum_profits_le_profit >= 1_i);

                                    proof.emit_proof_comment("define take both " + to_string(idx_pos) + "." + to_string(option_idx));
                                    auto [take_both_sums, _3, _4] = proof.create_proof_flag_reifying(
                                        WeightedPseudoBooleanSum{} + 1_i * take_sum_weights_ge_weight + 1_i * take_sum_profits_le_profit >= 2_i,
                                        "option_" + to_string(option_idx) + "_take_both_sums_" + to_string(idx_pos) + "_" + to_string(take_weight.raw_value) + "_" + to_string(take_profit.raw_value));
                                    proof.emit_rup_proof_line(take_lhs_both + 1_i * take_both_sums >= 1_i);

                                    take_weight_sum_if_permitted = take_sum_weights_ge_weight;
                                    take_profit_sum_if_permitted = take_sum_profits_le_profit;
                                    take_both_sums_if_permitted = take_both_sums;

                                    auto take = new_options.try_emplace(weight + weights.at(idx), tuple{profit + profits.at(idx), take_sum_weights_ge_weight, take_sum_profits_le_profit, take_both_sums, take_weight_line, take_profit_line}).first;
                                    get<0>(take->second) = max(get<0>(take->second), profit + profits.at(idx));
                                    if (get<0>(take->second) != profit + profits.at(idx))
                                        proof.emit_proof_comment("!!! found better profit 2");
                                }
                                else {
                                    // trail && current option -> no take
                                    proof.emit_proof_comment("!!! can't take");
                                }

                                proof.emit_proof_comment("*** must either take or no take option " + to_string(idx_pos) + "." + to_string(option_idx));

                                // trail && current option -> take option or not take option
                                auto trail_and_current_option = trail;
                                if (current_option_both)
                                    trail_and_current_option += 1_i * ! *current_option_both;

                                if (take_weight_sum_if_permitted)
                                    proof.emit_rup_proof_line(trail_and_current_option + 1_i * *take_weight_sum_if_permitted + 1_i * no_take_sum_weights_ge_weight >= 1_i);
                                else
                                    proof.emit_rup_proof_line(trail_and_current_option + 1_i * no_take_sum_weights_ge_weight >= 1_i);

                                if (take_profit_sum_if_permitted)
                                    proof.emit_rup_proof_line(trail_and_current_option + 1_i * *take_profit_sum_if_permitted + 1_i * no_take_sum_profits_le_profit >= 1_i);
                                else
                                    proof.emit_rup_proof_line(trail_and_current_option + 1_i * no_take_sum_profits_le_profit >= 1_i);

                                if (take_both_sums_if_permitted)
                                    proof.emit_rup_proof_line(trail_and_current_option + 1_i * *take_both_sums_if_permitted + 1_i * no_take_both_sums >= 1_i);
                                else
                                    proof.emit_rup_proof_line(trail_and_current_option + 1_i * no_take_both_sums >= 1_i);

                                options_at_current_level.push_back(no_take_both_sums);
                                if (take_both_sums_if_permitted)
                                    options_at_current_level.push_back(*take_both_sums_if_permitted);
                            }

                            // trail -> one of the new options
                            proof.emit_proof_comment("*** must take an option from this level " + to_string(idx_pos));
                            auto must_take_an_option = trail;
                            for (auto & flag : options_at_current_level)
                                must_take_an_option += 1_i * flag;
                            proof.emit_rup_proof_line(must_take_an_option >= 1_i);

                            options = move(new_options);
                        }
                    }}),
            PropagatorState::Enable};
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
