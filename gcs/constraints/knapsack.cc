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
using std::multimap;
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
        const vector<IntegerVariableID> & vars, IntegerVariableID weight_var, IntegerVariableID profit_var,
        const ProofLine opb_weight_line, const ProofLine opb_profit_line) -> pair<Inference, PropagatorState>
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
            auto inference = state.infer(weight_var == used_weight, NoJustificationNeeded{});
            if (inference != Inference::Contradiction)
                increase_inference_to(inference, state.infer(profit_var == accumulated_profit, NoJustificationNeeded{}));
            return pair{inference, PropagatorState::DisableUntilBacktrack};
        }

        auto inference = state.infer(profit_var >= accumulated_profit, NoJustificationNeeded{});
        if (Inference::Contradiction == inference)
            return pair{inference, PropagatorState::Enable};

        inference = state.infer(weight_var >= used_weight, NoJustificationNeeded{});
        if (Inference::Contradiction == inference)
            return pair{inference, PropagatorState::Enable};

        auto remaining_weight = state.upper_bound(weight_var) - used_weight;
        auto best_profit_bottom = knapsack_best_profit_bottom(weights, profits, vars, undetermined_vars, remaining_weight) + accumulated_profit;

        return pair{state.infer(profit_var < 1_i + best_profit_bottom, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                        auto trail = proof.trail_variables_as_sum(state, 1_i);

                        multimap<Integer, tuple<Integer, optional<ProofFlag>, optional<ProofFlag>, optional<ProofFlag>, optional<ProofLine>, optional<ProofLine>>> options;
                        options.emplace(0_i, tuple{0_i, nullopt, nullopt, nullopt, nullopt, nullopt});

                        for (const auto & [idx_pos, idx] : enumerate(undetermined_vars)) {
                            multimap<Integer, tuple<Integer, optional<ProofFlag>, optional<ProofFlag>, optional<ProofFlag>, optional<ProofLine>, optional<ProofLine>>> new_options;
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

                                vector<ProofFlag> take_weight_options, take_profit_options, take_both_options;
                                auto do_option = [&](bool take, const string & name, Integer new_weight, Integer new_profit) {
                                    auto opt_lhs_weight = trail, opt_lhs_profit = trail, opt_lhs_both = trail;
                                    if (current_option_weight)
                                        opt_lhs_weight += 1_i * ! *current_option_weight;
                                    if (current_option_profit)
                                        opt_lhs_profit += 1_i * ! *current_option_profit;
                                    if (current_option_both)
                                        opt_lhs_both += 1_i * ! *current_option_both;
                                    opt_lhs_weight += 1_i * (vars.at(idx) != (take ? 1_i : 0_i));
                                    opt_lhs_profit += 1_i * (vars.at(idx) != (take ? 1_i : 0_i));
                                    opt_lhs_both += 1_i * (vars.at(idx) != (take ? 1_i : 0_i));

                                    proof.emit_proof_comment("*** " + name + " option " + to_string(idx_pos) + "." + to_string(option_idx));
                                    proof.emit_proof_comment("define " + name + " >= weight " + to_string(idx_pos) + "." + to_string(option_idx));
                                    auto [opt_sum_weights_ge_weight, opt_weight_line, _1] = proof.create_proof_flag_reifying(
                                        sum_of_weights_so_far >= new_weight,
                                        "option_" + to_string(option_idx) + "_" + name + "_sum_" + to_string(idx_pos) + "_weights_ge_" + to_string(new_weight.raw_value));
                                    if (current_option_weight_line)
                                        proof.emit_proof_line("p -1 " + to_string(*current_option_weight_line) + " +");
                                    proof.emit_rup_proof_line(opt_lhs_weight + 1_i * opt_sum_weights_ge_weight >= 1_i);
                                    proof.emit_rup_proof_line(opt_lhs_both + 1_i * opt_sum_weights_ge_weight >= 1_i);

                                    proof.emit_proof_comment("define " + name + " <= profit " + to_string(idx_pos) + "." + to_string(option_idx));
                                    auto [opt_sum_profits_le_profit, opt_profit_line, _2] = proof.create_proof_flag_reifying(
                                        sum_of_profits_so_far <= new_profit,
                                        "option_" + to_string(option_idx) + "_" + name + "_sum_" + to_string(idx_pos) + "_profits_le_" + to_string(new_profit.raw_value));
                                    if (current_option_profit_line)
                                        proof.emit_proof_line("p -1 " + to_string(*current_option_profit_line) + " +");
                                    proof.emit_rup_proof_line(opt_lhs_profit + 1_i * opt_sum_profits_le_profit >= 1_i);
                                    proof.emit_rup_proof_line(opt_lhs_both + 1_i * opt_sum_profits_le_profit >= 1_i);

                                    proof.emit_proof_comment("define " + name + " both " + to_string(idx_pos) + "." + to_string(option_idx));
                                    auto [opt_both_sums, _3, _4] = proof.create_proof_flag_reifying(
                                        WeightedPseudoBooleanSum{} + 1_i * opt_sum_weights_ge_weight + 1_i * opt_sum_profits_le_profit >= 2_i,
                                        "option_" + to_string(option_idx) + "_" + name + "_both_sums_" + to_string(idx_pos) + "_" + to_string(new_weight.raw_value) + "_" + to_string(new_profit.raw_value));
                                    proof.emit_rup_proof_line(opt_lhs_both + 1_i * opt_both_sums >= 1_i);

                                    if (new_weight <= remaining_weight) {
                                        new_options.emplace(new_weight, tuple{new_profit, opt_sum_weights_ge_weight, opt_sum_profits_le_profit, opt_both_sums, opt_weight_line, opt_profit_line});
                                        take_weight_options.push_back(opt_sum_weights_ge_weight);
                                        take_profit_options.push_back(opt_sum_profits_le_profit);
                                        take_both_options.push_back(opt_both_sums);
                                        options_at_current_level.push_back(opt_both_sums);
                                    }
                                    else {
                                        proof.emit_proof_comment("infeasible state");
                                        overloaded{
                                            [&](const SimpleIntegerVariableID & var) {
                                                auto bound_line = proof.get_or_emit_pol_term_for_bound_in_bits(state, true, var, state.upper_bound(weight_var));
                                                overloaded{
                                                    [&](const string & bound_line) {
                                                        proof.emit_proof_line("p " + to_string(opt_weight_line) + " " + to_string(opb_weight_line) + " + " + bound_line + " +");
                                                    },
                                                    [&](const ProofLine & bound_line) {
                                                        proof.emit_proof_line("p " + to_string(opt_weight_line) + " " + to_string(opb_weight_line) + " + " + to_string(bound_line) + " +");
                                                    }}
                                                    .visit(bound_line);
                                            },
                                            [&](const ConstantIntegerVariableID &) {
                                            },
                                            [&](const ViewOfIntegerVariableID &) {
                                                throw UnimplementedException{};
                                            }}
                                            .visit(weight_var);
                                        proof.emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * ! opt_sum_weights_ge_weight >= 1_i);
                                        proof.emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * ! opt_both_sums >= 1_i);
                                    }
                                };

                                do_option(false, "excl", weight, profit);
                                do_option(true, "incl", weight + weights.at(idx), profit + profits.at(idx));

                                proof.emit_proof_comment("*** must either take or no take option " + to_string(idx_pos) + "." + to_string(option_idx));

                                // trail && current option -> take option or not take option
                                auto trail_and_current_option = trail;
                                if (current_option_both)
                                    trail_and_current_option += 1_i * ! *current_option_both;

                                auto combine = [&](const WeightedPseudoBooleanSum & sum, const vector<ProofFlag> & add) {
                                    auto result = sum;
                                    for (auto & a : add)
                                        result += 1_i * a;
                                    return result;
                                };

                                proof.emit_rup_proof_line(combine(trail_and_current_option, take_weight_options) >= 1_i);
                                proof.emit_rup_proof_line(combine(trail_and_current_option, take_profit_options) >= 1_i);
                                proof.emit_rup_proof_line(combine(trail_and_current_option, take_both_options) >= 1_i);
                            }

                            // trail -> one of the new options
                            proof.emit_proof_comment("*** must take an option from this level " + to_string(idx_pos));
                            auto must_take_an_option = trail;
                            for (auto & flag : options_at_current_level)
                                must_take_an_option += 1_i * flag;
                            proof.emit_rup_proof_line(must_take_an_option >= 1_i);

                            options = move(new_options);
                        }

                        proof.emit_proof_comment("*** no final option supports weight");
                        for (const auto & [weight, option_data] : options) {
                            const auto & [_1, _2, current_option_profit, _3, _4, current_option_profit_line] = option_data;
                            auto no_support = trail;
                            if (current_option_profit)
                                no_support += 1_i * ! *current_option_profit;
                            proof.emit_proof_line("p " + to_string(opb_profit_line) + " " + to_string(*current_option_profit_line) + " +");
                            proof.emit_rup_proof_line(no_support + 1_i * (profit_var < 1_i + best_profit_bottom) >= 1_i);
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

    optional<ProofLine> weight_line, profit_line;
    if (propagators.want_definitions()) {
        WeightedPseudoBooleanSum weights_eq, profits_eq;
        for (const auto & [idx, v] : enumerate(_vars)) {
            weights_eq += _weights[idx] * v;
            profits_eq += _profits[idx] * v;
        }
        weight_line = propagators.define(initial_state, weights_eq == 1_i * _weight).first;
        profit_line = propagators.define(initial_state, profits_eq == 1_i * _profit).second;
    }

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};
    triggers.on_change.emplace_back(_weight);
    triggers.on_change.emplace_back(_profit);

    propagators.install(
        [weights = move(_weights), profits = move(_profits), vars = move(_vars), weight = move(_weight),
            profit = move(_profit), weight_line = weight_line, profit_line = profit_line](State & state) -> pair<Inference, PropagatorState> {
            return knapsack(state, weights, profits, vars, weight, profit, *weight_line, *profit_line);
        },
        triggers, "knapsack");
}

auto Knapsack::describe_for_proof() -> std::string
{
    return "knapsack";
}
