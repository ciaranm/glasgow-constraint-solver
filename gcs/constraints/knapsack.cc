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

                        struct WeightData
                        {
                            ProofFlag flag;
                            ProofLine fwd_reification;
                            ProofLine rev_reification;
                        };

                        struct ProfitData
                        {
                            ProofFlag flag;
                            ProofLine fwd_reification;
                            ProofLine rev_reification;
                        };

                        struct StateData
                        {
                            bool feasible;
                            ProofFlag weight_flag;
                            ProofLine weight_line;
                            ProofFlag profit_flag;
                            ProofLine profit_line;
                            ProofFlag both_flag;
                        };

                        map<Integer, optional<WeightData>> parent_layer_weights;
                        map<Integer, optional<ProfitData>> parent_layer_profits;
                        map<pair<Integer, Integer>, optional<StateData>> parent_layer_states;

                        parent_layer_weights.emplace(0_i, nullopt);
                        parent_layer_profits.emplace(0_i, nullopt);
                        parent_layer_states.emplace(pair{0_i, 0_i}, nullopt);

                        WeightedPseudoBooleanSum sum_of_weights_so_far, sum_of_profits_so_far;

                        for (const auto & [idx_pos, idx] : enumerate(undetermined_vars)) {
                            map<Integer, optional<WeightData>> current_layer_weights;
                            map<Integer, optional<ProfitData>> current_layer_profits;
                            map<pair<Integer, Integer>, optional<StateData>> current_layer_states;

                            sum_of_weights_so_far += weights.at(idx) * vars.at(idx);
                            sum_of_profits_so_far += profits.at(idx) * vars.at(idx);

                            for (const auto & [weight_and_profit, state_data] : parent_layer_states) {
                                if (state_data && ! state_data->feasible)
                                    continue;

                                const auto & [weight, profit] = weight_and_profit;

                                vector<ProofFlag> current_node_weight_children, current_node_profit_children, current_node_state_children;
                                auto do_option = [&](bool take, const string & name, Integer new_weight, Integer new_profit) {
                                    auto opt_lhs_weight = trail, opt_lhs_profit = trail, opt_lhs_both = trail;
                                    if (state_data) {
                                        opt_lhs_weight += 1_i * ! state_data->weight_flag;
                                        opt_lhs_profit += 1_i * ! state_data->profit_flag;
                                        opt_lhs_both += 1_i * ! state_data->both_flag;
                                    }
                                    opt_lhs_weight += 1_i * (vars.at(idx) != (take ? 1_i : 0_i));
                                    opt_lhs_profit += 1_i * (vars.at(idx) != (take ? 1_i : 0_i));
                                    opt_lhs_both += 1_i * (vars.at(idx) != (take ? 1_i : 0_i));

                                    auto weight_data = current_layer_weights.find(new_weight);
                                    if (weight_data == current_layer_weights.end()) {
                                        proof.emit_proof_comment("define " + name + " >= weight " + to_string(idx_pos));
                                        auto [flag, fwd_reification, rev_reification] = proof.create_proof_flag_reifying(
                                            sum_of_weights_so_far >= new_weight,
                                            "sum_" + to_string(idx_pos) + "_weights_ge_" + to_string(new_weight.raw_value));
                                        weight_data = current_layer_weights.emplace(
                                                                               new_weight, WeightData{
                                                                                               .flag = flag,                       //
                                                                                               .fwd_reification = fwd_reification, //
                                                                                               .rev_reification = rev_reification  //
                                                                                           })
                                                          .first;
                                    }

                                    if (state_data && weight_data->second)
                                        proof.emit_proof_line("p " + to_string(weight_data->second->rev_reification) + " " + to_string(state_data->weight_line) + " +");
                                    proof.emit_rup_proof_line(opt_lhs_weight + 1_i * weight_data->second->flag >= 1_i);
                                    proof.emit_rup_proof_line(opt_lhs_both + 1_i * weight_data->second->flag >= 1_i);

                                    auto profit_data = current_layer_profits.find(new_profit);
                                    if (profit_data == current_layer_profits.end()) {
                                        proof.emit_proof_comment("define " + name + " <= profit " + to_string(idx_pos));
                                        auto [flag, fwd_reification, rev_reification] = proof.create_proof_flag_reifying(
                                            sum_of_profits_so_far <= new_profit,
                                            "sum_" + to_string(idx_pos) + "_profits_le_" + to_string(new_profit.raw_value));
                                        profit_data = current_layer_profits.emplace(
                                                                               new_profit, ProfitData{
                                                                                               .flag = flag,                       //
                                                                                               .fwd_reification = fwd_reification, //
                                                                                               .rev_reification = rev_reification  //
                                                                                           })
                                                          .first;
                                    }
                                    if (state_data && profit_data->second)
                                        proof.emit_proof_line("p " + to_string(profit_data->second->rev_reification) + " " + to_string(state_data->profit_line) + " +");
                                    proof.emit_rup_proof_line(opt_lhs_profit + 1_i * profit_data->second->flag >= 1_i);
                                    proof.emit_rup_proof_line(opt_lhs_both + 1_i * profit_data->second->flag >= 1_i);

                                    auto new_state_data = current_layer_states.find(pair{new_weight, new_profit});
                                    if (new_state_data == current_layer_states.end()) {
                                        proof.emit_proof_comment("define " + name + " both " + to_string(idx_pos));
                                        auto [flag, _1, _2] = proof.create_proof_flag_reifying(
                                            WeightedPseudoBooleanSum{} + 1_i * weight_data->second->flag + 1_i * profit_data->second->flag >= 2_i,
                                            "both_sums_" + to_string(idx_pos) + "_" + to_string(new_weight.raw_value) + "_" + to_string(new_profit.raw_value));
                                        new_state_data = current_layer_states.emplace(
                                                                                 pair{new_weight, new_profit}, StateData{
                                                                                                                   .feasible = (new_weight <= remaining_weight),        //
                                                                                                                   .weight_flag = weight_data->second->flag,            //
                                                                                                                   .weight_line = weight_data->second->fwd_reification, //
                                                                                                                   .profit_flag = profit_data->second->flag,            //
                                                                                                                   .profit_line = profit_data->second->fwd_reification, //
                                                                                                                   .both_flag = flag                                    //
                                                                                                               })
                                                             .first;
                                    }
                                    proof.emit_rup_proof_line(opt_lhs_both + 1_i * new_state_data->second->both_flag >= 1_i);

                                    if (new_state_data->second->feasible) {
                                        current_node_weight_children.push_back(weight_data->second->flag);
                                        current_node_profit_children.push_back(profit_data->second->flag);
                                        current_node_state_children.push_back(new_state_data->second->both_flag);
                                    }
                                    else {
                                        proof.emit_proof_comment("infeasible state: new weight is " + to_string(new_weight.raw_value) +
                                            " but remaining is " + to_string(remaining_weight.raw_value));
                                        overloaded{
                                            [&](const SimpleIntegerVariableID & var) {
                                                auto bound_line = proof.get_or_emit_pol_term_for_bound_in_bits(state, true, var, state.upper_bound(weight_var));
                                                overloaded{
                                                    [&](const string & bound_line) {
                                                        proof.emit_proof_line("p " + to_string(weight_data->second->fwd_reification) + " " + to_string(opb_weight_line) + " + " + bound_line + " +");
                                                    },
                                                    [&](const ProofLine & bound_line) {
                                                        proof.emit_proof_line("p " + to_string(weight_data->second->fwd_reification) + " " + to_string(opb_weight_line) + " + " + to_string(bound_line) + " +");
                                                    }}
                                                    .visit(bound_line);
                                            },
                                            [&](const ConstantIntegerVariableID &) {
                                            },
                                            [&](const ViewOfIntegerVariableID &) {
                                                throw UnimplementedException{};
                                            }}
                                            .visit(weight_var);
                                        proof.emit_rup_proof_line(trail + 1_i * ! weight_data->second->flag >= 1_i);
                                        proof.emit_rup_proof_line(trail + 1_i * ! new_state_data->second->both_flag >= 1_i);
                                    }
                                };

                                do_option(false, "excl", weight, profit);
                                do_option(true, "incl", weight + weights.at(idx), profit + profits.at(idx));

                                proof.emit_proof_comment("*** must either take or no take option " + to_string(idx_pos));

                                // trail && current option -> take option or not take option
                                auto trail_and_current_option = trail;
                                if (state_data)
                                    trail_and_current_option += 1_i * ! state_data->both_flag;

                                auto combine = [&](const WeightedPseudoBooleanSum & sum, const vector<ProofFlag> & add) {
                                    auto result = sum;
                                    for (auto & a : add)
                                        result += 1_i * a;
                                    return result;
                                };

                                proof.emit_rup_proof_line(combine(trail_and_current_option, current_node_weight_children) >= 1_i);
                                proof.emit_rup_proof_line(combine(trail_and_current_option, current_node_profit_children) >= 1_i);
                                proof.emit_rup_proof_line(combine(trail_and_current_option, current_node_state_children) >= 1_i);
                            }

                            // trail -> one of the new options
                            proof.emit_proof_comment("*** must take an option from this level " + to_string(idx_pos));
                            auto must_take_an_option = trail;
                            for (const auto & [_, child] : current_layer_states)
                                if (child->feasible)
                                    must_take_an_option += 1_i * child->both_flag;
                            proof.emit_rup_proof_line(must_take_an_option >= 1_i);

                            parent_layer_weights = move(current_layer_weights);
                            parent_layer_profits = move(current_layer_profits);
                            parent_layer_states = move(current_layer_states);
                        }

                        proof.emit_proof_comment("*** no final option supports weight");
                        for (const auto & [_, state] : parent_layer_states) {
                            if (! state || ! state->feasible)
                                continue;

                            auto no_support = trail + 1_i * ! state->profit_flag;
                            proof.emit_proof_line("p " + to_string(opb_profit_line) + " " + to_string(state->profit_line) + " +");
                            proof.emit_rup_proof_line(no_support + 1_i * (profit_var < 1_i + best_profit_bottom) >= 1_i);
                        }
                        proof.emit_rup_proof_line(trail + 1_i * (profit_var < 1_i + best_profit_bottom) >= 1_i);
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
