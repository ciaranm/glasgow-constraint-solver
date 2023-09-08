#include <gcs/constraints/knapsack.hh>
#include <gcs/exception.hh>
#include <gcs/innards/opb_utils.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <tuple>
#include <type_traits>

using namespace gcs;
using namespace gcs::innards;

using std::conditional_t;
using std::invoke;
using std::make_unique;
using std::map;
using std::max;
using std::minmax_element;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
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
    auto prepare_and_get_bound_p_term(State & state, IntegerVariableID var) -> string
    {
        return overloaded{
            [&](const SimpleIntegerVariableID & var) -> string {
                auto bound_line = state.maybe_proof()->get_or_emit_pol_term_for_bound_in_bits(state, true, var, state.upper_bound(var));
                return overloaded{
                    [&](const string & bound_line) -> string {
                        return bound_line;
                    },
                    [&](const ProofLine & bound_line) -> string {
                        return to_string(bound_line);
                    }}
                    .visit(bound_line);
            },
            [&](const ConstantIntegerVariableID &) -> string {
                throw UnimplementedException{};
            },
            [&](const ViewOfIntegerVariableID &) -> string {
                throw UnimplementedException{};
            }}
            .visit(var);
    }

    struct NoData
    {
    };

    struct NodeInequalityData
    {
        ProofFlag reif_flag;
        ProofLine forward_reif_line;
        ProofLine reverse_reif_line;
    };

    struct FullNodeData
    {
        ProofFlag reif_flag;
        ProofFlag weight_reif_flag;
        ProofLine forward_reif_for_weight_line;
        ProofFlag profit_reif_flag;
        ProofLine forward_reif_for_profit_line;
    };

    template <bool doing_proof_>
    auto knapsack_bc(
        State & state,
        Integer committed_weight, Integer committed_profit,
        pair<Integer, Integer> weight_bounds,
        pair<Integer, Integer> profit_bounds,
        const vector<Integer> & weights, const vector<Integer> & profits,
        IntegerVariableID weight_var, IntegerVariableID profit_var,
        const vector<IntegerVariableID> & all_vars, const vector<size_t> & undetermined_var_indices,
        ProofLine opb_weight_line, ProofLine opb_profit_line) -> Inference
    {
        using NodeInequalityData = conditional_t<doing_proof_, NodeInequalityData, NoData>;
        using FullNodeData = conditional_t<doing_proof_, FullNodeData, NoData>;

        map<pair<Integer, Integer>, optional<FullNodeData>> completed_layer_nodes;
        completed_layer_nodes.emplace(pair{0_i, 0_i}, nullopt);

        auto scoped_proof_sublevel [[maybe_unused]] = 0;
        if constexpr (doing_proof_) {
            scoped_proof_sublevel = state.maybe_proof()->proof_level();
            state.maybe_proof()->enter_proof_level(scoped_proof_sublevel + 1);
        }

        WeightedPseudoBooleanSum sum_of_weights_so_far, sum_of_profits_so_far, trail;
        if constexpr (doing_proof_) {
            trail = state.maybe_proof()->trail_variables_as_sum(state, 1_i);
            state.maybe_proof()->emit_proof_comment("starting knapsack");
        }

        for (const auto & [layer_number, var_idx] : enumerate(undetermined_var_indices)) {
            sum_of_weights_so_far += weights.at(var_idx) * all_vars.at(var_idx);
            sum_of_profits_so_far += profits.at(var_idx) * all_vars.at(var_idx);

            map<pair<Integer, Integer>, optional<FullNodeData>> growing_layer_nodes;
            map<Integer, NodeInequalityData> growing_layer_weights_data, growing_layer_profits_data;

            for (auto & [weight_and_profit, completed_node_data] : completed_layer_nodes) {
                auto [weight, profit] = weight_and_profit;

                PseudoBooleanTerm not_in_weight_state = FalseLiteral{}, not_in_profit_state = FalseLiteral{}, not_in_full_state = FalseLiteral{};
                if constexpr (doing_proof_) {
                    if (completed_node_data) {
                        not_in_weight_state = ! completed_node_data->weight_reif_flag;
                        not_in_profit_state = ! completed_node_data->profit_reif_flag;
                        not_in_full_state = ! completed_node_data->reif_flag;
                    }
                }

                vector<Integer> feasible_choices;
                vector<ProofFlag> feasible_weight_flags, feasible_profit_flags, feasible_node_flags;

                state.for_each_value(all_vars.at(var_idx), [&](Integer val) {
                    auto new_weight = weight + val * weights.at(var_idx);
                    auto new_profit = profit + val * profits.at(var_idx);

                    if constexpr (! doing_proof_) {
                        if (committed_weight + new_weight <= weight_bounds.second && committed_profit + new_profit <= profit_bounds.second)
                            growing_layer_nodes.emplace(pair{new_weight, new_profit}, nullopt);
                    }
                    else {
                        auto weight_data = growing_layer_weights_data.find(new_weight);
                        if (weight_data == growing_layer_weights_data.end()) {
                            auto [flag, fwd, rev] = state.maybe_proof()->create_proof_flag_reifying(
                                sum_of_weights_so_far >= new_weight, "s" + to_string(layer_number) + "w" + to_string(new_weight.raw_value));
                            weight_data = growing_layer_weights_data.emplace(new_weight, NodeInequalityData{flag, fwd, rev}).first;
                        }

                        auto profit_data = growing_layer_profits_data.find(new_profit);
                        if (profit_data == growing_layer_profits_data.end()) {
                            auto [flag, fwd, rev] = state.maybe_proof()->create_proof_flag_reifying(
                                sum_of_profits_so_far <= new_profit, "s" + to_string(layer_number) + "p" + to_string(new_profit.raw_value));
                            profit_data = growing_layer_profits_data.emplace(new_profit, NodeInequalityData{flag, fwd, rev}).first;
                        }

                        auto node_data = growing_layer_nodes.find(pair{new_weight, new_profit});
                        if (node_data == growing_layer_nodes.end()) {
                            auto [flag, _1, _2] = state.maybe_proof()->create_proof_flag_reifying(
                                WeightedPseudoBooleanSum{} + 1_i * weight_data->second.reif_flag + 1_i * profit_data->second.reif_flag >= 2_i,
                                "s" + to_string(layer_number) + "w" + to_string(new_weight.raw_value) + "p" + to_string(new_profit.raw_value));
                            node_data = growing_layer_nodes.emplace(pair{new_weight, new_profit}, FullNodeData{flag, weight_data->second.reif_flag, weight_data->second.forward_reif_line, profit_data->second.reif_flag, profit_data->second.forward_reif_line}).first;
                        }

                        auto not_choice = all_vars.at(var_idx) != val;

                        state.maybe_proof()->emit_proof_comment("weight state");
                        if (completed_node_data)
                            state.maybe_proof()->emit_proof_line("p " +
                                to_string(weight_data->second.reverse_reif_line) + " " +
                                to_string(completed_node_data->forward_reif_for_weight_line) + " +");
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_weight_state + 1_i * not_choice + 1_i * weight_data->second.reif_flag >= 1_i);
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * weight_data->second.reif_flag >= 1_i);

                        state.maybe_proof()->emit_proof_comment("profit state");
                        if (completed_node_data)
                            state.maybe_proof()->emit_proof_line("p " +
                                to_string(profit_data->second.reverse_reif_line) + " " +
                                to_string(completed_node_data->forward_reif_for_profit_line) + " +");
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_profit_state + 1_i * not_choice + 1_i * profit_data->second.reif_flag >= 1_i);
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * profit_data->second.reif_flag >= 1_i);

                        state.maybe_proof()->emit_proof_comment("both state");
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * node_data->second->reif_flag >= 1_i);

                        if (committed_weight + new_weight > weight_bounds.second) {
                            state.maybe_proof()->emit_proof_comment("infeasible weight");
                            auto weight_var_str = prepare_and_get_bound_p_term(state, weight_var);
                            state.maybe_proof()->emit_proof_line("p " + to_string(weight_data->second.forward_reif_line) + " " + to_string(opb_weight_line) + " + " + weight_var_str + " +");
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_weight_state + 1_i * not_choice >= 1_i);
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice >= 1_i);
                        }
                        else if (committed_profit + new_profit > profit_bounds.second) {
                            state.maybe_proof()->emit_proof_comment("infeasible profit");
                            auto profit_var_str = prepare_and_get_bound_p_term(state, profit_var);
                            state.maybe_proof()->emit_proof_line("p " + to_string(profit_data->second.forward_reif_line) + " " + to_string(opb_profit_line) + " + " + profit_var_str + " +");
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_profit_state + 1_i * not_choice >= 1_i);
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice >= 1_i);
                        }
                        else {
                            feasible_choices.push_back(val);
                            feasible_weight_flags.push_back(weight_data->second.reif_flag);
                            feasible_profit_flags.push_back(profit_data->second.reif_flag);
                            feasible_node_flags.push_back(node_data->second->reif_flag);
                        }
                    }
                });

                if constexpr (doing_proof_) {
                    state.maybe_proof()->emit_proof_comment("select from feasible choices for child");
                    WeightedPseudoBooleanSum must_pick_one = trail + 1_i * not_in_full_state;
                    auto must_pick_one_val = must_pick_one, must_pick_one_weight = must_pick_one, must_pick_one_profit = must_pick_one, must_pick_one_node = must_pick_one;
                    for (auto & f : feasible_choices)
                        must_pick_one_val += 1_i * (all_vars.at(var_idx) == f);
                    for (auto & f : feasible_weight_flags)
                        must_pick_one_weight += 1_i * f;
                    for (auto & f : feasible_profit_flags)
                        must_pick_one_profit += 1_i * f;
                    for (auto & f : feasible_node_flags)
                        must_pick_one_node += 1_i * f;

                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_val >= 1_i);
                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_weight >= 1_i);
                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_profit >= 1_i);
                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_node >= 1_i);
                }
            }

            erase_if(growing_layer_nodes, [&](const auto & item) {
                const auto & [weight_and_profit, _] = item;
                const auto & [weight, profit] = weight_and_profit;
                return committed_weight + weight > weight_bounds.second || committed_profit + profit > profit_bounds.second;
            });

            if constexpr (doing_proof_) {
                state.maybe_proof()->emit_proof_comment("select from feasible choices for layer");
                WeightedPseudoBooleanSum must_pick_one = trail;
                for (auto & [_, data] : growing_layer_nodes)
                    must_pick_one += 1_i * data->reif_flag;
                state.maybe_proof()->emit_rup_proof_line(must_pick_one >= 1_i);
            }

            completed_layer_nodes = move(growing_layer_nodes);
        }

        if constexpr (doing_proof_) {
            state.maybe_proof()->enter_proof_level(scoped_proof_sublevel);
        }

        if (completed_layer_nodes.empty()) {
            if constexpr (doing_proof_) {
                state.maybe_proof()->emit_proof_comment("no feasible terminal states remaining");
                state.maybe_proof()->forget_proof_level(scoped_proof_sublevel + 1);
            }
            return Inference::Contradiction;
        }

        auto [lowest_profit, highest_profit] = minmax_element(completed_layer_nodes.begin(), completed_layer_nodes.end(),
            [&](const pair<pair<Integer, Integer>, optional<FullNodeData>> & a,
                const pair<pair<Integer, Integer>, optional<FullNodeData>> & b) { return a.first.second < b.first.second; });

        auto result = state.infer(profit_var < committed_profit + highest_profit->first.second + 1_i, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) {
            if constexpr (doing_proof_) {
                state.maybe_proof()->emit_proof_comment("select from feasible terminal states");
                for (auto & [_, data] : completed_layer_nodes) {
                    auto no_support = trail + 1_i * ! data->profit_reif_flag;
                    proof.emit_proof_line("p " + to_string(opb_profit_line) + " " + to_string(data->forward_reif_for_profit_line) + " +");
                    proof.emit_rup_proof_line(no_support + 1_i * (profit_var < 1_i + committed_profit + highest_profit->first.second) >= 1_i);
                }
            }
            proof.emit_rup_proof_line(trail + 1_i * (profit_var < 1_i + committed_profit + highest_profit->first.second) >= 1_i);
        }});

        if constexpr (doing_proof_) {
            state.maybe_proof()->forget_proof_level(scoped_proof_sublevel + 1);
        }

        return result;
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

        if (state.maybe_proof())
            return pair{knapsack_bc<true>(state, used_weight, accumulated_profit, state.bounds(weight_var), state.bounds(profit_var),
                            weights, profits, weight_var, profit_var, vars, undetermined_vars, opb_weight_line, opb_profit_line),
                PropagatorState::Enable};
        else
            return pair{knapsack_bc<false>(state, used_weight, accumulated_profit, state.bounds(weight_var), state.bounds(profit_var),
                            weights, profits, weight_var, profit_var, vars, undetermined_vars, opb_weight_line, opb_profit_line),
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
