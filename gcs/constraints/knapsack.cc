#include <gcs/constraints/knapsack.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <list>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <type_traits>

using namespace gcs;
using namespace gcs::innards;

using std::conditional_t;
using std::list;
using std::make_unique;
using std::map;
using std::minmax_element;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

Knapsack::Knapsack(vector<Integer> weights, vector<Integer> profits,
    vector<IntegerVariableID> vars, IntegerVariableID weight, IntegerVariableID profit) :
    _coeffs({move(weights), move(profits)}),
    _vars(move(vars)),
    _totals({weight, profit})
{
}

Knapsack::Knapsack(vector<vector<Integer>> coefficients,
    vector<IntegerVariableID> vars,
    vector<IntegerVariableID> totals) :
    _coeffs(move(coefficients)),
    _vars(move(vars)),
    _totals(move(totals))
{
}

auto Knapsack::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Knapsack>(_coeffs, _vars, _totals);
}

namespace
{
    auto prepare_and_get_bound_p_term(const State & state, ProofLogger * const logger, IntegerVariableID var, bool upper) -> string
    {
        return overloaded{
            [&](const SimpleIntegerVariableID & var) -> string {
                return overloaded{
                    [&](const ProofLine & line) { return to_string(line); },
                    [&](const string & s) { return s; }}
                    .visit(logger->variable_constraints_tracker().need_pol_item_defining_literal(upper ? var < state.upper_bound(var) + 1_i : var >= state.lower_bound(var)));
            },
            [&](const ConstantIntegerVariableID &) -> string {
                throw UnimplementedException{};
            },
            [&](const ViewOfIntegerVariableID &) -> string {
                throw UnimplementedException{};
            }}
            .visit(var);
    }

    template <bool doing_proof_>
    auto knapsack_gac(
        const State & state,
        ProofLogger * const logger,
        const vector<IntegerVariableID> & reason_variables,
        auto & inference,
        const vector<Integer> & committed,
        const vector<pair<Integer, Integer>> & bounds,
        const vector<vector<Integer>> & coeffs,
        const vector<IntegerVariableID> & totals,
        const vector<IntegerVariableID> & vars_including_assigned, const vector<size_t> & undetermined_var_indices,
        const optional<vector<pair<ProofLine, ProofLine>>> & opb_lines) -> void
    {
        struct NodeInequalityData
        {
            ProofFlag reif_flag;
            ProofLine forward_reif_line;
            ProofLine reverse_reif_line;
        };

        struct FullNodeData
        {
            optional<ProofFlag> reif_flag;
            vector<NodeInequalityData> ges;
            vector<NodeInequalityData> les;
            vector<pair<vector<Integer>, Integer>> predecessors;
        };

        list<map<vector<Integer>, optional<FullNodeData>>> completed_layers;
        completed_layers.emplace_back();
        completed_layers.back().emplace(vector(totals.size(), 0_i), nullopt);

        vector<WeightedPseudoBooleanSum> sums_so_far(coeffs.size());

        // for each variable in turn...
        for (const auto & [the_layer_number, the_var_idx] : enumerate(undetermined_var_indices)) {
            const auto & layer_number = the_layer_number; // clang
            const auto & var_idx = the_var_idx; // clang

            for (const auto & [idx, c] : enumerate(coeffs))
                sums_so_far.at(idx) += c.at(var_idx) * vars_including_assigned.at(var_idx);

            map<vector<Integer>, optional<FullNodeData>> growing_layer_nodes;
            vector<map<Integer, NodeInequalityData>> growing_layer_ge_datas(totals.size()), growing_layer_le_datas(totals.size());
            set<Integer> supported_values;

            // for each state on the prior layer...
            for (auto & [the_sums, the_completed_node_data] : completed_layers.back()) {
                const auto & sums = the_sums;                               // clang...
                auto & completed_node_data = the_completed_node_data;       // clang...

                vector<PseudoBooleanTerm> not_in_ge_states(totals.size(), FalseLiteral{}), not_in_le_states(totals.size(), FalseLiteral{});
                PseudoBooleanTerm not_in_full_state = FalseLiteral{};
                if constexpr (doing_proof_) {
                    if (completed_node_data) {
                        for (const auto & [x, _] : enumerate(totals)) {
                            not_in_ge_states.at(x) = ! completed_node_data->ges.at(x).reif_flag;
                            not_in_le_states.at(x) = ! completed_node_data->les.at(x).reif_flag;
                        }
                        not_in_full_state = ! *completed_node_data->reif_flag;
                    }
                }

                vector<Integer> feasible_choices;
                vector<vector<ProofFlag>> feasible_ge_flags(totals.size()), feasible_le_flags(totals.size());
                vector<ProofFlag> feasible_node_flags;

                // for each value in this variable's value...
                for (auto val : state.each_value_mutable(vars_including_assigned.at(var_idx))) {
                    // for each equation, calculate the partial sums of all the
                    // variables up to and including this one.
                    vector<Integer> new_sums(totals.size(), 0_i);
                    for (const auto & [x, v] : enumerate(totals))
                        new_sums.at(x) = sums.at(x) + val * coeffs.at(x).at(var_idx);

                    if constexpr (! doing_proof_) {
                        // because everything is non-negative, we can eliminate states where the
                        // partial sum is already too large.
                        bool bounds_violation = false;
                        for (const auto & [x, _] : enumerate(totals)) {
                            if (committed.at(x) + new_sums.at(x) > bounds.at(x).second) {
                                bounds_violation = true;
                                break;
                            }
                        }

                        auto node_data = growing_layer_nodes.emplace(new_sums, FullNodeData{{}, {}, {}, {}}).first;
                        node_data->second->predecessors.emplace_back(sums, val);

                        // because everything is non-negative, we can eliminate states where the
                        // partial sum is already too large.
                        bool eliminated = false;
                        for (const auto & [x, _] : enumerate(totals)) {
                            if (committed.at(x) + new_sums.at(x) > bounds.at(x).second) {
                                eliminated = true;
                                break;
                            }
                        }

                        if (! eliminated) {
                            feasible_choices.push_back(val);
                            supported_values.emplace(val);
                        }
                    }
                    else {
                        // build up extension variables representing partial sum >= actual value and
                        // partial sum <= actual value for each equation.
                        vector<typename map<Integer, NodeInequalityData>::const_iterator> ge_datas, le_datas;
                        for (const auto & [x, _] : enumerate(totals)) {
                            auto ge_data = growing_layer_ge_datas.at(x).find(new_sums.at(x));
                            if (ge_data == growing_layer_ge_datas.at(x).end()) {
                                auto [flag, fwd, rev] = logger->create_proof_flag_reifying(
                                    sums_so_far.at(x) >= new_sums.at(x), "s" + to_string(layer_number) + "x" + to_string(x) + "ge" + to_string(new_sums.at(x).raw_value),
                                    ProofLevel::Temporary);
                                ge_data = growing_layer_ge_datas.at(x).emplace(new_sums.at(x), NodeInequalityData{flag, fwd, rev}).first;
                            }
                            ge_datas.push_back(ge_data);

                            auto le_data = growing_layer_le_datas.at(x).find(new_sums.at(x));
                            if (le_data == growing_layer_le_datas.at(x).end()) {
                                auto [flag, fwd, rev] = logger->create_proof_flag_reifying(
                                    sums_so_far.at(x) <= new_sums.at(x), "s" + to_string(layer_number) + "x" + to_string(x) + "le" + to_string(new_sums.at(x).raw_value),
                                    ProofLevel::Temporary);
                                le_data = growing_layer_le_datas.at(x).emplace(new_sums.at(x), NodeInequalityData{flag, fwd, rev}).first;
                            }
                            le_datas.push_back(le_data);
                        }

                        // build an extension variable representing our entire
                        // state, which is that each partial sum is both >= and
                        // <= its actual value
                        auto node_data = growing_layer_nodes.find(new_sums);
                        if (node_data == growing_layer_nodes.end()) {
                            vector<NodeInequalityData> les, ges;
                            WeightedPseudoBooleanSum all;
                            string name;
                            for (auto & l : le_datas) {
                                all += 1_i * l->second.reif_flag;
                                name += "_";
                                name += to_string(l->first.raw_value);
                                les.push_back(l->second);
                            }
                            for (auto & g : ge_datas) {
                                all += 1_i * g->second.reif_flag;
                                ges.push_back(g->second);
                            }

                            auto [flag, _1, _2] = logger->create_proof_flag_reifying(all >= Integer(all.terms.size()),
                                "s" + to_string(layer_number) + "x" + name, ProofLevel::Temporary);
                            node_data = growing_layer_nodes.emplace(new_sums, FullNodeData{flag, ges, les, {}}).first;
                        }
                        node_data->second->predecessors.emplace_back(sums, val);

                        auto not_choice = vars_including_assigned.at(var_idx) != val;

                        // show that if we were in our parent state, and made the current branching
                        // choice, then our new state variables must be true.
                        for (const auto & [x, _] : enumerate(totals)) {
                            // current choices and branch -> partial sum >= value
                            if (completed_node_data)
                                logger->emit_proof_line("p " +
                                        to_string(ge_datas.at(x)->second.reverse_reif_line) + " " +
                                        to_string(completed_node_data->ges.at(x).forward_reif_line) + " +",
                                    ProofLevel::Temporary);
                            logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                                WeightedPseudoBooleanSum{} + 1_i * not_in_ge_states.at(x) + 1_i * not_choice + 1_i * ge_datas.at(x)->second.reif_flag >= 1_i,
                                ProofLevel::Temporary);
                            logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                                WeightedPseudoBooleanSum{} + 1_i * not_in_full_state + 1_i * not_choice + 1_i * ge_datas.at(x)->second.reif_flag >= 1_i,
                                ProofLevel::Temporary);

                            // current choices and branch -> partial sum <= value
                            if (completed_node_data)
                                logger->emit_proof_line("p " +
                                        to_string(le_datas.at(x)->second.reverse_reif_line) + " " +
                                        to_string(completed_node_data->les.at(x).forward_reif_line) + " +",
                                    ProofLevel::Temporary);
                            logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                                WeightedPseudoBooleanSum{} + 1_i * not_in_le_states.at(x) + 1_i * not_choice + 1_i * le_datas.at(x)->second.reif_flag >= 1_i,
                                ProofLevel::Temporary);
                            logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                                WeightedPseudoBooleanSum{} + 1_i * not_in_full_state + 1_i * not_choice + 1_i * le_datas.at(x)->second.reif_flag >= 1_i,
                                ProofLevel::Temporary);
                        }

                        // current choices and branch -> current state
                        logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                            WeightedPseudoBooleanSum{} + 1_i * not_in_full_state + 1_i * not_choice + 1_i * *node_data->second->reif_flag >= 1_i,
                            ProofLevel::Temporary);

                        // because everything is non-negative, we can eliminate states where the
                        // partial sum is already too large.
                        bool eliminated = false;
                        for (const auto & [x, _] : enumerate(totals)) {
                            if (committed.at(x) + new_sums.at(x) > bounds.at(x).second) {
                                auto weight_var_str = prepare_and_get_bound_p_term(state, logger, totals.at(x), true);
                                logger->emit_proof_line("p " + to_string(ge_datas.at(x)->second.forward_reif_line) + " " +
                                        to_string(opb_lines->at(x).first) + " + " + weight_var_str + " +",
                                    ProofLevel::Temporary);
                                logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                                    WeightedPseudoBooleanSum{} + 1_i * not_in_ge_states.at(x) + 1_i * not_choice >= 1_i,
                                    ProofLevel::Temporary);
                                logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                                    WeightedPseudoBooleanSum{} + 1_i * not_in_full_state + 1_i * not_choice >= 1_i,
                                    ProofLevel::Temporary);
                                eliminated = true;
                                break;
                            }
                        }

                        if (! eliminated) {
                            feasible_choices.push_back(val);
                            for (const auto & [x, _] : enumerate(totals)) {
                                feasible_le_flags.at(x).push_back(le_datas.at(x)->second.reif_flag);
                                feasible_ge_flags.at(x).push_back(ge_datas.at(x)->second.reif_flag);
                            }
                            feasible_node_flags.push_back(*node_data->second->reif_flag);
                            supported_values.emplace(val);
                        }
                    }
                }

                if constexpr (doing_proof_) {
                    // we must select at least one feasible choice from this variable's values
                    WeightedPseudoBooleanSum must_pick_one = WeightedPseudoBooleanSum{} + 1_i * not_in_full_state;
                    WeightedPseudoBooleanSum must_pick_one_val = must_pick_one, must_pick_one_node = must_pick_one;

                    for (auto & f : feasible_choices)
                        must_pick_one_val += 1_i * (vars_including_assigned.at(var_idx) == f);
                    logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                        must_pick_one_val >= 1_i, ProofLevel::Temporary);

                    for (const auto & [x, _] : enumerate(totals)) {
                        auto must_pick_one_le = must_pick_one, must_pick_one_ge = must_pick_one;
                        for (auto & f : feasible_le_flags.at(x))
                            must_pick_one_le += 1_i * f;
                        for (auto & f : feasible_ge_flags.at(x))
                            must_pick_one_ge += 1_i * f;
                        logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables), must_pick_one_le >= 1_i, ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables), must_pick_one_ge >= 1_i, ProofLevel::Temporary);
                    }

                    for (auto & f : feasible_node_flags)
                        must_pick_one_node += 1_i * f;
                    logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables), must_pick_one_node >= 1_i, ProofLevel::Temporary);
                }
            }

            // because everything is non-negative, we can eliminate states where the
            // partial sum is already too large.
            erase_if(growing_layer_nodes, [&](const auto & item) {
                const auto & [sums, _] = item;
                for (const auto & [x, _] : enumerate(totals))
                    if (committed.at(x) + sums.at(x) > bounds.at(x).second)
                        return true;
                return false;
            });

            if constexpr (doing_proof_) {
                // we must select at least one of the feasible states from the layer we've just built
                logger->emit_proof_comment("select from feasible choices for layer");
                WeightedPseudoBooleanSum must_pick_one;
                for (auto & [_, data] : growing_layer_nodes)
                    must_pick_one += 1_i * *data->reif_flag;
                logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables), must_pick_one >= 1_i, ProofLevel::Temporary);
            }

            // we might have some values that never allowed a state to be created
            for (auto val : state.each_value_mutable(vars_including_assigned.at(var_idx))) {
                if (! supported_values.contains(val)) {
                    if constexpr (doing_proof_) {
                        logger->emit_proof_comment("unsupported value on forward pass");
                        for (auto & [_, data] : growing_layer_nodes) {
                            logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                                WeightedPseudoBooleanSum{} + 1_i * ! *data->reif_flag + 1_i * (vars_including_assigned.at(var_idx) != val) >= 1_i,
                                ProofLevel::Temporary);
                        }
                    }
                    inference.infer(logger, vars_including_assigned.at(var_idx) != val, JustifyUsingRUP{},
                        generic_reason(state, reason_variables));
                }
            }

            completed_layers.emplace_back(move(growing_layer_nodes));
        }

        // states where the sum is too large are already gone, but we might
        // have remaining states where the final sum is too small.
        for (auto final_states_iter = completed_layers.back().begin(), final_states_iter_end = completed_layers.back().end(); final_states_iter != final_states_iter_end;) {
            bool eliminated = false;
            for (const auto & [x, _] : enumerate(totals)) {
                if (committed.at(x) + final_states_iter->first.at(x) < bounds.at(x).first) {
                    if constexpr (doing_proof_) {
                        auto weight_var_str = prepare_and_get_bound_p_term(state, logger, totals.at(x), false);
                        logger->emit_proof_line("p " + to_string(final_states_iter->second->les.at(x).forward_reif_line) +
                                " " + to_string(opb_lines->at(x).second) + " + " + weight_var_str + " +",
                            ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                            WeightedPseudoBooleanSum{} + 1_i * ! final_states_iter->second->les.at(x).reif_flag >= 1_i,
                            ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                            WeightedPseudoBooleanSum{} + 1_i * ! *final_states_iter->second->reif_flag >= 1_i,
                            ProofLevel::Temporary);
                    }
                    completed_layers.back().erase(final_states_iter++);
                    eliminated = true;
                    break;
                }
            }

            if (! eliminated)
                ++final_states_iter;
        }

        // same again, but for interior values that are not bounds
        for (auto final_states_iter = completed_layers.back().begin(), final_states_iter_end = completed_layers.back().end(); final_states_iter != final_states_iter_end;) {
            bool eliminated = false;
            for (const auto & [x, _] : enumerate(totals)) {
                auto val = committed.at(x) + final_states_iter->first.at(x);
                if (! state.in_domain(totals.at(x), val)) {
                    if constexpr (doing_proof_) {
                        logger->emit_proof_line("p " + to_string(final_states_iter->second->les.at(x).forward_reif_line) +
                                " " + to_string(opb_lines->at(x).second) + " +",
                            ProofLevel::Temporary);
                        logger->emit_proof_line("p " + to_string(final_states_iter->second->ges.at(x).forward_reif_line) +
                                " " + to_string(opb_lines->at(x).first) + " +",
                            ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                            WeightedPseudoBooleanSum{} + 1_i * ! *final_states_iter->second->reif_flag + 1_i * (totals.at(x) == val) >= 1_i,
                            ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                            WeightedPseudoBooleanSum{} + 1_i * ! *final_states_iter->second->reif_flag >= 1_i,
                            ProofLevel::Temporary);
                    }
                    completed_layers.back().erase(final_states_iter++);
                    eliminated = true;
                    break;
                }
            }

            if (! eliminated)
                ++final_states_iter;
        }

        if (completed_layers.back().empty()) {
            if constexpr (doing_proof_) {
                logger->emit_proof_comment("no feasible choices remaining");
                logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables), WeightedPseudoBooleanSum{} >= 1_i, ProofLevel::Temporary);
            }

            inference.contradiction(logger, JustifyUsingRUP{}, generic_reason(state, reason_variables));
        }
        else {
            vector<Literal> inferences;
            for (const auto & [the_x, _] : enumerate(totals)) {
                auto x = the_x; // clang
                auto [lowest_iter, highest_iter] = minmax_element(completed_layers.back().begin(), completed_layers.back().end(),
                    [&](const pair<vector<Integer>, optional<FullNodeData>> & a,
                        const pair<vector<Integer>, optional<FullNodeData>> & b) { return a.first.at(x) < b.first.at(x); });

                auto lowest = lowest_iter->first.at(x);
                inferences.emplace_back(totals.at(x) >= committed.at(x) + lowest);

                auto highest = highest_iter->first.at(x);
                inferences.emplace_back(totals.at(x) < committed.at(x) + highest + 1_i);

                for (auto v : state.each_value_immutable(totals.at(x))) {
                    if (v >= committed.at(x) + lowest && v < committed.at(x) + highest + 1_i)
                        if (completed_layers.back().end() == find_if(completed_layers.back().begin(), completed_layers.back().end(), [&](const pair<vector<Integer>, optional<FullNodeData>> & a) {
                                return a.first.at(x) + committed.at(x) == v;
                            }))
                            inferences.emplace_back(totals.at(x) != v);
                }

                if constexpr (doing_proof_) {
                    logger->emit_proof_comment("select from feasible terminal states");
                    for (auto & [_, data] : completed_layers.back()) {
                        if (! data.has_value())
                            continue;

                        auto no_support_ge = WeightedPseudoBooleanSum{} + 1_i * ! data->ges.at(x).reif_flag;
                        logger->emit_proof_line("p " + to_string(opb_lines->at(x).first) + " " + to_string(data->ges.at(x).forward_reif_line) + " +",
                            ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                            no_support_ge + 1_i * (totals.at(x) >= committed.at(x) + lowest) >= 1_i,
                            ProofLevel::Temporary);

                        auto no_support_le = WeightedPseudoBooleanSum{} + 1_i * ! data->les.at(x).reif_flag;
                        logger->emit_proof_line("p " + to_string(opb_lines->at(x).second) + " " + to_string(data->les.at(x).forward_reif_line) + " +",
                            ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                            no_support_le + 1_i * (totals.at(x) < 1_i + committed.at(x) + highest) >= 1_i,
                            ProofLevel::Temporary);
                    }

                    logger->emit_proof_comment("deduce overall conclusions");
                    logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                        WeightedPseudoBooleanSum{} + 1_i * (totals.at(x) >= committed.at(x) + lowest) >= 1_i,
                        ProofLevel::Temporary);
                    logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                        WeightedPseudoBooleanSum{} + 1_i * (totals.at(x) < 1_i + committed.at(x) + highest) >= 1_i,
                        ProofLevel::Temporary);
                }
            }

            inference.infer_all(logger, inferences, JustifyUsingRUP{}, generic_reason(state, reason_variables));

            // now run backwards from the final state, eliminating states that
            // didn't lead to a feasible terminal state, and seeing if any
            // further values lose support
            int var_number = undetermined_var_indices.size() - 1;
            for (auto layer = completed_layers.rbegin(); layer != completed_layers.rend() && next(layer) != completed_layers.rend(); ++layer, --var_number) {
                set<vector<Integer>> reached;
                set<Integer> supported;
                for (const auto & [_, data] : *layer) {
                    for (const auto & [sums, val] : data->predecessors) {
                        reached.insert(sums);
                        supported.insert(val);
                    }
                }

                for (auto state_iter = next(layer)->begin(), state_iter_end = next(layer)->end(); state_iter != state_iter_end;) {
                    if (reached.contains(state_iter->first))
                        ++state_iter;
                    else {
                        if constexpr (doing_proof_)
                            if (state_iter->second->reif_flag)
                                logger->emit_rup_proof_line_under_reason(generic_reason(state, reason_variables),
                                    WeightedPseudoBooleanSum{} + 1_i * ! *state_iter->second->reif_flag >= 1_i,
                                    ProofLevel::Temporary);
                        next(layer)->erase(state_iter++);
                    }
                }

                auto var = vars_including_assigned.at(undetermined_var_indices.at(var_number));
                for (auto val : state.each_value_mutable(var)) {
                    if (! supported.contains(val))
                        inference.infer(logger, var != val, JustifyUsingRUP{}, generic_reason(state, reason_variables));
                }
            }
        }
    }

    auto knapsack(
        const State & state,
        ProofLogger * const logger,
        auto & inference,
        const vector<vector<Integer>> & coeffs,
        const vector<IntegerVariableID> & vars,
        const vector<IntegerVariableID> & totals,
        const vector<pair<ProofLine, ProofLine>> & eqn_lines) -> PropagatorState
    {
        vector<size_t> undetermined_vars;
        vector<Integer> committed_sums(totals.size(), 0_i);
        for (const auto & [idx, v] : enumerate(vars)) {
            auto val = state.optional_single_value(v);
            if (! val)
                undetermined_vars.push_back(idx);
            else
                for (const auto & [x, _] : enumerate(committed_sums))
                    committed_sums.at(x) += *val * coeffs.at(x).at(idx);
        }

        if (undetermined_vars.empty()) {
            Literals all_vars_assigned;
            for (auto & v : vars)
                all_vars_assigned.push_back(v == state(v));

            for (const auto & [x, t] : enumerate(totals)) {
                inference.infer(logger, totals.at(x) == committed_sums.at(x), JustifyUsingRUP{}, [=]() { return all_vars_assigned; });
            }
        }

        for (const auto & [x, v] : enumerate(totals))
            inference.infer(logger, v >= committed_sums.at(x), JustifyUsingRUP{}, generic_reason(state, vars));

        vector<pair<Integer, Integer>> boundses;
        for (auto & t : totals)
            boundses.emplace_back(state.bounds(t));

        int temporary_proof_level = 0;
        if (logger)
            temporary_proof_level = logger->temporary_proof_level();

        vector<IntegerVariableID> reason_variables;
        reason_variables.insert(reason_variables.end(), vars.begin(), vars.end());
        reason_variables.insert(reason_variables.end(), totals.begin(), totals.end());
        if (logger)
            knapsack_gac<true>(state, logger, reason_variables, inference, committed_sums,
                boundses, coeffs, totals, vars, undetermined_vars, eqn_lines);
        else
            knapsack_gac<false>(state, logger, reason_variables, inference, committed_sums,
                boundses, coeffs, totals, vars, undetermined_vars, nullopt);

        if (logger)
            logger->forget_proof_level(temporary_proof_level);

        return PropagatorState::Enable;
    }
}

auto Knapsack::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (_coeffs.size() != _totals.size())
        throw UnexpectedException{"mismatch between coefficients and totals sizes for knapsack"};

    if (_coeffs.empty())
        throw UnexpectedException{"empty knapsack coefficients"};
    unsigned n_vars = _coeffs.begin()->size();

    for (auto & c : _coeffs)
        if (c.size() != n_vars)
            throw UnexpectedException{"not sure what to do about different coefficient array sizes for knapsack"};

    for (auto & cc : _coeffs)
        for (auto & c : cc)
            if (c < 0_i)
                throw UnexpectedException{"not sure what to do about negative coefficients for knapsack"};

    for (auto & v : _vars)
        if (initial_state.lower_bound(v) < 0_i)
            throw UnexpectedException{"can only support non-negative variables for knapsack"};

    for (auto & t : _totals)
        if (initial_state.lower_bound(t) < 0_i)
            throw UnexpectedException{"not sure what to do about negative permitted totals for knapsack"};

    vector<pair<ProofLine, ProofLine>> eqns_lines;
    if (optional_model) {
        for (const auto & [cc_idx, cc] : enumerate(_coeffs)) {
            WeightedPseudoBooleanSum sum_eq;
            for (const auto & [idx, v] : enumerate(_vars))
                sum_eq += cc.at(idx) * v;
            auto [eq1, eq2] = optional_model->add_constraint(sum_eq == 1_i * _totals.at(cc_idx));
            eqns_lines.emplace_back(eq1.value(), eq2.value());
        }
    }

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};
    triggers.on_change.insert(triggers.on_change.end(), _totals.begin(), _totals.end());

    propagators.install(
        [coeffs = move(_coeffs), vars = move(_vars), totals = move(_totals), eqns_lines = move(eqns_lines)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return knapsack(state, logger, inference, coeffs, vars, totals, eqns_lines);
        },
        triggers, "knapsack");
}

auto Knapsack::describe_for_proof() -> string
{
    return "knapsack";
}
