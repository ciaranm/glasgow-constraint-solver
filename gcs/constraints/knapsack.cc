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
    auto prepare_and_get_bound_p_term(State & state, IntegerVariableID var, bool upper) -> string
    {
        return overloaded{
            [&](const SimpleIntegerVariableID & var) -> string {
                auto bound_line = state.maybe_proof()->get_or_emit_pol_term_for_bound_in_bits(state, upper,
                    var, upper ? state.upper_bound(var) : state.lower_bound(var));
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
        ProofFlag weight_ge_reif_flag;
        ProofLine forward_reif_for_weight_ge_line;
        ProofFlag weight_le_reif_flag;
        ProofLine forward_reif_for_weight_le_line;
        ProofFlag profit_ge_reif_flag;
        ProofLine forward_reif_for_profit_ge_line;
        ProofFlag profit_le_reif_flag;
        ProofLine forward_reif_for_profit_le_line;
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
        const pair<ProofLine, ProofLine> & opb_weight_lines, const pair<ProofLine, ProofLine> & opb_profit_lines) -> Inference
    {
        using NodeInequalityData = conditional_t<doing_proof_, NodeInequalityData, NoData>;
        using FullNodeData = conditional_t<doing_proof_, FullNodeData, NoData>;

        map<pair<Integer, Integer>, optional<FullNodeData>> completed_layer_nodes;
        completed_layer_nodes.emplace(pair{0_i, 0_i}, nullopt);

        WeightedPseudoBooleanSum sum_of_weights_so_far, sum_of_profits_so_far, trail;
        if constexpr (doing_proof_) {
            trail = state.maybe_proof()->trail_variables_as_sum(state, 1_i);
            state.maybe_proof()->emit_proof_comment("starting knapsack");
        }

        for (const auto & [layer_number, var_idx] : enumerate(undetermined_var_indices)) {
            sum_of_weights_so_far += weights.at(var_idx) * all_vars.at(var_idx);
            sum_of_profits_so_far += profits.at(var_idx) * all_vars.at(var_idx);

            map<pair<Integer, Integer>, optional<FullNodeData>> growing_layer_nodes;
            map<Integer, NodeInequalityData> growing_layer_weights_ge_data, growing_layer_weights_le_data, growing_layer_profits_ge_data, growing_layer_profits_le_data;

            for (auto & [weight_and_profit, completed_node_data] : completed_layer_nodes) {
                auto [weight, profit] = weight_and_profit;

                PseudoBooleanTerm not_in_weight_ge_state = FalseLiteral{}, not_in_weight_le_state = FalseLiteral{},
                                  not_in_profit_ge_state = FalseLiteral{}, not_in_profit_le_state = FalseLiteral{},
                                  not_in_full_state = FalseLiteral{};
                if constexpr (doing_proof_) {
                    if (completed_node_data) {
                        not_in_weight_ge_state = ! completed_node_data->weight_ge_reif_flag;
                        not_in_weight_le_state = ! completed_node_data->weight_le_reif_flag;
                        not_in_profit_ge_state = ! completed_node_data->profit_ge_reif_flag;
                        not_in_profit_le_state = ! completed_node_data->profit_le_reif_flag;
                        not_in_full_state = ! completed_node_data->reif_flag;
                    }
                }

                vector<Integer> feasible_choices;
                vector<ProofFlag> feasible_weight_ge_flags, feasible_weight_le_flags, feasible_profit_ge_flags, feasible_profit_le_flags, feasible_node_flags;

                state.for_each_value(all_vars.at(var_idx), [&](Integer val) {
                    auto new_weight = weight + val * weights.at(var_idx);
                    auto new_profit = profit + val * profits.at(var_idx);

                    if constexpr (! doing_proof_) {
                        if (committed_weight + new_weight <= weight_bounds.second && committed_profit + new_profit <= profit_bounds.second)
                            growing_layer_nodes.emplace(pair{new_weight, new_profit}, nullopt);
                    }
                    else {
                        auto weight_ge_data = growing_layer_weights_ge_data.find(new_weight);
                        if (weight_ge_data == growing_layer_weights_ge_data.end()) {
                            auto [flag, fwd, rev] = state.maybe_proof()->create_proof_flag_reifying(
                                sum_of_weights_so_far >= new_weight, "s" + to_string(layer_number) + "wge" + to_string(new_weight.raw_value));
                            weight_ge_data = growing_layer_weights_ge_data.emplace(new_weight, NodeInequalityData{flag, fwd, rev}).first;
                        }

                        auto weight_le_data = growing_layer_weights_le_data.find(new_weight);
                        if (weight_le_data == growing_layer_weights_le_data.end()) {
                            auto [flag, fwd, rev] = state.maybe_proof()->create_proof_flag_reifying(
                                sum_of_weights_so_far <= new_weight, "s" + to_string(layer_number) + "wle" + to_string(new_weight.raw_value));
                            weight_le_data = growing_layer_weights_le_data.emplace(new_weight, NodeInequalityData{flag, fwd, rev}).first;
                        }

                        auto profit_ge_data = growing_layer_profits_ge_data.find(new_profit);
                        if (profit_ge_data == growing_layer_profits_ge_data.end()) {
                            auto [flag, fwd, rev] = state.maybe_proof()->create_proof_flag_reifying(
                                sum_of_profits_so_far >= new_profit, "s" + to_string(layer_number) + "pge" + to_string(new_profit.raw_value));
                            profit_ge_data = growing_layer_profits_ge_data.emplace(new_profit, NodeInequalityData{flag, fwd, rev}).first;
                        }

                        auto profit_le_data = growing_layer_profits_le_data.find(new_profit);
                        if (profit_le_data == growing_layer_profits_le_data.end()) {
                            auto [flag, fwd, rev] = state.maybe_proof()->create_proof_flag_reifying(
                                sum_of_profits_so_far <= new_profit, "s" + to_string(layer_number) + "ple" + to_string(new_profit.raw_value));
                            profit_le_data = growing_layer_profits_le_data.emplace(new_profit, NodeInequalityData{flag, fwd, rev}).first;
                        }

                        auto node_data = growing_layer_nodes.find(pair{new_weight, new_profit});
                        if (node_data == growing_layer_nodes.end()) {
                            auto [flag, _1, _2] = state.maybe_proof()->create_proof_flag_reifying(
                                WeightedPseudoBooleanSum{} + 1_i * weight_ge_data->second.reif_flag + 1_i * weight_le_data->second.reif_flag +
                                        1_i * profit_le_data->second.reif_flag + 1_i * profit_ge_data->second.reif_flag >=
                                    4_i,
                                "s" + to_string(layer_number) + "w" + to_string(new_weight.raw_value) + "p" + to_string(new_profit.raw_value));
                            node_data = growing_layer_nodes.emplace(pair{new_weight, new_profit}, FullNodeData{flag, weight_ge_data->second.reif_flag, weight_ge_data->second.forward_reif_line, weight_le_data->second.reif_flag, weight_le_data->second.forward_reif_line, profit_ge_data->second.reif_flag, profit_ge_data->second.forward_reif_line, profit_le_data->second.reif_flag, profit_le_data->second.forward_reif_line}).first;
                        }

                        auto not_choice = all_vars.at(var_idx) != val;

                        state.maybe_proof()->emit_proof_comment("weight ge state");
                        if (completed_node_data)
                            state.maybe_proof()->emit_proof_line("p " +
                                to_string(weight_ge_data->second.reverse_reif_line) + " " +
                                to_string(completed_node_data->forward_reif_for_weight_ge_line) + " +");
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_weight_ge_state + 1_i * not_choice + 1_i * weight_ge_data->second.reif_flag >= 1_i);
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * weight_ge_data->second.reif_flag >= 1_i);

                        state.maybe_proof()->emit_proof_comment("weight le state");
                        if (completed_node_data)
                            state.maybe_proof()->emit_proof_line("p " +
                                to_string(weight_le_data->second.reverse_reif_line) + " " +
                                to_string(completed_node_data->forward_reif_for_weight_le_line) + " +");
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_weight_le_state + 1_i * not_choice + 1_i * weight_le_data->second.reif_flag >= 1_i);
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * weight_le_data->second.reif_flag >= 1_i);

                        state.maybe_proof()->emit_proof_comment("profit le state");
                        if (completed_node_data)
                            state.maybe_proof()->emit_proof_line("p " +
                                to_string(profit_le_data->second.reverse_reif_line) + " " +
                                to_string(completed_node_data->forward_reif_for_profit_le_line) + " +");
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_profit_le_state + 1_i * not_choice + 1_i * profit_le_data->second.reif_flag >= 1_i);
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * profit_le_data->second.reif_flag >= 1_i);

                        state.maybe_proof()->emit_proof_comment("profit ge state");
                        if (completed_node_data)
                            state.maybe_proof()->emit_proof_line("p " +
                                to_string(profit_ge_data->second.reverse_reif_line) + " " +
                                to_string(completed_node_data->forward_reif_for_profit_ge_line) + " +");
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_profit_ge_state + 1_i * not_choice + 1_i * profit_ge_data->second.reif_flag >= 1_i);
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * profit_ge_data->second.reif_flag >= 1_i);

                        state.maybe_proof()->emit_proof_comment("all state");
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * node_data->second->reif_flag >= 1_i);

                        // because everything is non-negative, we can eliminate states where the
                        // partial sum is already too large.
                        if (committed_weight + new_weight > weight_bounds.second) {
                            state.maybe_proof()->emit_proof_comment("infeasible weight");
                            auto weight_var_str = prepare_and_get_bound_p_term(state, weight_var, true);
                            state.maybe_proof()->emit_proof_line("p " + to_string(weight_ge_data->second.forward_reif_line) + " " + to_string(opb_weight_lines.first) + " + " + weight_var_str + " +");
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_weight_ge_state + 1_i * not_choice >= 1_i);
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice >= 1_i);
                        }
                        else if (committed_profit + new_profit > profit_bounds.second) {
                            state.maybe_proof()->emit_proof_comment("infeasible profit");
                            auto profit_var_str = prepare_and_get_bound_p_term(state, profit_var, true);
                            state.maybe_proof()->emit_proof_line("p " + to_string(profit_ge_data->second.forward_reif_line) + " " + to_string(opb_profit_lines.first) + " + " + profit_var_str + " +");
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_profit_ge_state + 1_i * not_choice >= 1_i);
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice >= 1_i);
                        }
                        else {
                            feasible_choices.push_back(val);
                            feasible_weight_ge_flags.push_back(weight_ge_data->second.reif_flag);
                            feasible_weight_le_flags.push_back(weight_le_data->second.reif_flag);
                            feasible_profit_ge_flags.push_back(profit_ge_data->second.reif_flag);
                            feasible_profit_le_flags.push_back(profit_le_data->second.reif_flag);
                            feasible_node_flags.push_back(node_data->second->reif_flag);
                        }
                    }
                });

                if constexpr (doing_proof_) {
                    state.maybe_proof()->emit_proof_comment("select from feasible choices for child");
                    WeightedPseudoBooleanSum must_pick_one = trail + 1_i * not_in_full_state;
                    auto must_pick_one_val = must_pick_one, must_pick_one_weight_ge = must_pick_one, must_pick_one_weight_le = must_pick_one,
                         must_pick_one_profit_le = must_pick_one, must_pick_one_profit_ge = must_pick_one, must_pick_one_node = must_pick_one;
                    for (auto & f : feasible_choices)
                        must_pick_one_val += 1_i * (all_vars.at(var_idx) == f);
                    for (auto & f : feasible_weight_ge_flags)
                        must_pick_one_weight_ge += 1_i * f;
                    for (auto & f : feasible_weight_le_flags)
                        must_pick_one_weight_le += 1_i * f;
                    for (auto & f : feasible_profit_ge_flags)
                        must_pick_one_profit_ge += 1_i * f;
                    for (auto & f : feasible_profit_le_flags)
                        must_pick_one_profit_le += 1_i * f;
                    for (auto & f : feasible_node_flags)
                        must_pick_one_node += 1_i * f;

                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_val >= 1_i);
                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_weight_ge >= 1_i);
                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_weight_le >= 1_i);
                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_profit_ge >= 1_i);
                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_profit_le >= 1_i);
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

        // states where the sum is too large are already gone, but we might
        // have remaining states where the final sum is too small.
        for (auto final_states_iter = completed_layer_nodes.begin(), final_states_iter_end = completed_layer_nodes.end();
             final_states_iter != final_states_iter_end;) {
            if (committed_profit + final_states_iter->first.second < profit_bounds.first) {
                if constexpr (doing_proof_) {
                    state.maybe_proof()->emit_proof_comment("infeasible state due to profit being too low");
                    auto profit_var_str = prepare_and_get_bound_p_term(state, profit_var, false);
                    state.maybe_proof()->emit_proof_line("p " + to_string(final_states_iter->second->forward_reif_for_profit_le_line) +
                        " " + to_string(opb_profit_lines.second) + " + " + profit_var_str + " +");
                    state.maybe_proof()->emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * ! final_states_iter->second->profit_le_reif_flag >= 1_i);
                    state.maybe_proof()->emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * ! final_states_iter->second->reif_flag >= 1_i);
                }
                completed_layer_nodes.erase(final_states_iter++);
            }
            else if (committed_weight + final_states_iter->first.first < weight_bounds.first) {
                if constexpr (doing_proof_) {
                    state.maybe_proof()->emit_proof_comment("infeasible state due to weight being too low");
                    auto weight_var_str = prepare_and_get_bound_p_term(state, weight_var, false);
                    state.maybe_proof()->emit_proof_line("p " + to_string(final_states_iter->second->forward_reif_for_weight_le_line) +
                        " " + to_string(opb_weight_lines.second) + " + " + weight_var_str + " +");
                    state.maybe_proof()->emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * ! final_states_iter->second->weight_le_reif_flag >= 1_i);
                    state.maybe_proof()->emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * ! final_states_iter->second->reif_flag >= 1_i);
                }
                completed_layer_nodes.erase(final_states_iter++);
            }
            else {
                ++final_states_iter;
            }
        }

        if (completed_layer_nodes.empty()) {
            if constexpr (doing_proof_) {
                state.maybe_proof()->emit_proof_comment("no feasible choices remaining");
                state.maybe_proof()->emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} >= 1_i);
            }

            return Inference::Contradiction;
        }
        else {
            auto [lowest_weight_iter, highest_weight_iter] = minmax_element(completed_layer_nodes.begin(), completed_layer_nodes.end(),
                [&](const pair<pair<Integer, Integer>, optional<FullNodeData>> & a,
                    const pair<pair<Integer, Integer>, optional<FullNodeData>> & b) { return a.first.first < b.first.first; });
            auto [lowest_profit_iter, highest_profit_iter] = minmax_element(completed_layer_nodes.begin(), completed_layer_nodes.end(),
                [&](const pair<pair<Integer, Integer>, optional<FullNodeData>> & a,
                    const pair<pair<Integer, Integer>, optional<FullNodeData>> & b) { return a.first.second < b.first.second; });
            auto lowest_weight = lowest_weight_iter->first.first;
            auto highest_weight = highest_weight_iter->first.first;
            auto lowest_profit = lowest_profit_iter->first.second;
            auto highest_profit = highest_profit_iter->first.second;

            if constexpr (doing_proof_) {
                state.maybe_proof()->emit_proof_comment("select from feasible terminal states");
                for (auto & [_, data] : completed_layer_nodes) {
                    auto no_support_weight_ge = trail + 1_i * ! data->weight_ge_reif_flag;
                    state.maybe_proof()->emit_proof_line("p " + to_string(opb_weight_lines.first) + " " + to_string(data->forward_reif_for_weight_ge_line) + " +");
                    state.maybe_proof()->emit_rup_proof_line(no_support_weight_ge + 1_i * (weight_var >= committed_weight + lowest_weight) >= 1_i);

                    auto no_support_weight_le = trail + 1_i * ! data->weight_le_reif_flag;
                    state.maybe_proof()->emit_proof_line("p " + to_string(opb_weight_lines.first) + " " + to_string(data->forward_reif_for_weight_le_line) + " +");
                    state.maybe_proof()->emit_rup_proof_line(no_support_weight_le + 1_i * (weight_var < 1_i + committed_weight + lowest_weight) >= 1_i);

                    auto no_support_profit_ge = trail + 1_i * ! data->profit_ge_reif_flag;
                    state.maybe_proof()->emit_proof_line("p " + to_string(opb_profit_lines.first) + " " + to_string(data->forward_reif_for_profit_ge_line) + " +");
                    state.maybe_proof()->emit_rup_proof_line(no_support_profit_ge + 1_i * (profit_var >= committed_profit + lowest_profit) >= 1_i);

                    auto no_support_profit_le = trail + 1_i * ! data->profit_le_reif_flag;
                    state.maybe_proof()->emit_proof_line("p " + to_string(opb_profit_lines.second) + " " + to_string(data->forward_reif_for_profit_le_line) + " +");
                    state.maybe_proof()->emit_rup_proof_line(no_support_profit_le + 1_i * (profit_var < 1_i + committed_profit + highest_profit) >= 1_i);
                }

                state.maybe_proof()->emit_proof_comment("deduce overall conclusions");
                state.maybe_proof()->emit_rup_proof_line(trail + 1_i * (weight_var >= committed_weight + lowest_weight) >= 1_i);
                state.maybe_proof()->emit_rup_proof_line(trail + 1_i * (weight_var < 1_i + committed_weight + highest_weight) >= 1_i);
                state.maybe_proof()->emit_rup_proof_line(trail + 1_i * (profit_var >= committed_profit + lowest_profit) >= 1_i);
                state.maybe_proof()->emit_rup_proof_line(trail + 1_i * (profit_var < 1_i + committed_profit + highest_profit) >= 1_i);
            }

            return state.infer_all({profit_var < committed_profit + highest_profit + 1_i,
                                       profit_var >= committed_profit + lowest_profit,
                                       weight_var < committed_weight + highest_weight + 1_i,
                                       weight_var >= committed_weight + lowest_weight},
                JustifyUsingRUP{});
        }
    }

    auto knapsack(State & state, const vector<Integer> & weights, const vector<Integer> & profits,
        const vector<IntegerVariableID> & vars, IntegerVariableID weight_var, IntegerVariableID profit_var,
        const pair<ProofLine, ProofLine> & opb_weight_lines, const pair<ProofLine, ProofLine> & opb_profit_lines) -> pair<Inference, PropagatorState>
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
                            weights, profits, weight_var, profit_var, vars, undetermined_vars, opb_weight_lines, opb_profit_lines),
                PropagatorState::Enable};
        else
            return pair{knapsack_bc<false>(state, used_weight, accumulated_profit, state.bounds(weight_var), state.bounds(profit_var),
                            weights, profits, weight_var, profit_var, vars, undetermined_vars, opb_weight_lines, opb_profit_lines),
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

    pair<optional<ProofLine>, optional<ProofLine>> weight_lines, profit_lines;
    if (propagators.want_definitions()) {
        WeightedPseudoBooleanSum weights_eq, profits_eq;
        for (const auto & [idx, v] : enumerate(_vars)) {
            weights_eq += _weights[idx] * v;
            profits_eq += _profits[idx] * v;
        }
        weight_lines = propagators.define(initial_state, weights_eq == 1_i * _weight);
        profit_lines = propagators.define(initial_state, profits_eq == 1_i * _profit);
    }

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};
    triggers.on_change.emplace_back(_weight);
    triggers.on_change.emplace_back(_profit);

    propagators.install(
        [weights = move(_weights), profits = move(_profits), vars = move(_vars), weight = move(_weight),
            profit = move(_profit), weight_lines = weight_lines, profit_lines = profit_lines](State & state) -> pair<Inference, PropagatorState> {
            return knapsack(state, weights, profits, vars, weight, profit, {weight_lines.first.value(), weight_lines.second.value()},
                {profit_lines.first.value(), profit_lines.second.value()});
        },
        triggers, "knapsack");
}

auto Knapsack::describe_for_proof() -> std::string
{
    return "knapsack";
}
