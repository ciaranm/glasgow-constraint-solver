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
        vector<NodeInequalityData> ges;
        vector<NodeInequalityData> les;
    };

    template <bool doing_proof_>
    auto knapsack_bc(
        State & state,
        const vector<Integer> & committed,
        const vector<pair<Integer, Integer>> & bounds,
        const vector<vector<Integer>> & coeffs,
        const vector<IntegerVariableID> & totals,
        const vector<IntegerVariableID> & all_vars, const vector<size_t> & undetermined_var_indices,
        const optional<vector<pair<ProofLine, ProofLine>>> & opb_lines) -> Inference
    {
        using NodeInequalityData = conditional_t<doing_proof_, NodeInequalityData, NoData>;
        using FullNodeData = conditional_t<doing_proof_, FullNodeData, NoData>;

        auto inference = Inference::NoChange;

        map<vector<Integer>, optional<FullNodeData>> completed_layer_nodes;
        completed_layer_nodes.emplace(vector(totals.size(), 0_i), nullopt);

        WeightedPseudoBooleanSum trail;
        if constexpr (doing_proof_) {
            trail = state.maybe_proof()->trail_variables_as_sum(state, 1_i);
        }

        vector<WeightedPseudoBooleanSum> sums_so_far(coeffs.size());

        // for each variable in turn...
        for (const auto & [the_layer_number, the_var_idx] : enumerate(undetermined_var_indices)) {
            const auto & layer_number = the_layer_number; // clang
            const auto & var_idx = the_var_idx; // clang

            for (const auto & [idx, c] : enumerate(coeffs))
                sums_so_far.at(idx) += c.at(var_idx) * all_vars.at(var_idx);

            map<vector<Integer>, optional<FullNodeData>> growing_layer_nodes;
            vector<map<Integer, NodeInequalityData>> growing_layer_ge_datas(totals.size()), growing_layer_le_datas(totals.size());
            set<Integer> supported_values;

            // for each state on the prior layer...
            for (const auto & [the_sums, the_completed_node_data] : completed_layer_nodes) {
                const auto & sums = the_sums;                               // clang...
                const auto & completed_node_data = the_completed_node_data; // clang...

                vector<PseudoBooleanTerm> not_in_ge_states(totals.size(), FalseLiteral{}), not_in_le_states(totals.size(), FalseLiteral{});
                PseudoBooleanTerm not_in_full_state = FalseLiteral{};
                if constexpr (doing_proof_) {
                    if (completed_node_data) {
                        for (const auto & [x, _] : enumerate(totals)) {
                            not_in_ge_states.at(x) = ! completed_node_data->ges.at(x).reif_flag;
                            not_in_le_states.at(x) = ! completed_node_data->les.at(x).reif_flag;
                        }
                        not_in_full_state = ! completed_node_data->reif_flag;
                    }
                }

                vector<Integer> feasible_choices;
                vector<vector<ProofFlag>> feasible_ge_flags(totals.size()), feasible_le_flags(totals.size());
                vector<ProofFlag> feasible_node_flags;

                // for each value in this variable's value...
                state.for_each_value(all_vars.at(var_idx), [&](Integer val) {
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

                        // if we're feasible, add us to the growing layer
                        if (! bounds_violation)
                            growing_layer_nodes.emplace(new_sums, nullopt);
                    }
                    else {
                        // build up extension variables representing partial sum >= actual value and
                        // partial sum <= actual value for each equation.
                        vector<typename map<Integer, NodeInequalityData>::const_iterator> ge_datas, le_datas;
                        for (const auto & [x, _] : enumerate(totals)) {
                            auto ge_data = growing_layer_ge_datas.at(x).find(new_sums.at(x));
                            if (ge_data == growing_layer_ge_datas.at(x).end()) {
                                auto [flag, fwd, rev] = state.maybe_proof()->create_proof_flag_reifying(
                                    sums_so_far.at(x) >= new_sums.at(x), "s" + to_string(layer_number) + "x" + to_string(x) + "ge" + to_string(new_sums.at(x).raw_value),
                                    ProofLevel::Temporary);
                                ge_data = growing_layer_ge_datas.at(x).emplace(new_sums.at(x), NodeInequalityData{flag, fwd, rev}).first;
                            }
                            ge_datas.push_back(ge_data);

                            auto le_data = growing_layer_le_datas.at(x).find(new_sums.at(x));
                            if (le_data == growing_layer_le_datas.at(x).end()) {
                                auto [flag, fwd, rev] = state.maybe_proof()->create_proof_flag_reifying(
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

                            auto [flag, _1, _2] = state.maybe_proof()->create_proof_flag_reifying(all >= Integer(all.terms.size()),
                                "s" + to_string(layer_number) + "x" + name, ProofLevel::Temporary);
                            node_data = growing_layer_nodes.emplace(new_sums, FullNodeData{flag, ges, les}).first;
                        }

                        auto not_choice = all_vars.at(var_idx) != val;

                        // show that if we were in our parent state, and made the current branching
                        // choice, then our new state variables must be true.
                        for (const auto & [x, _] : enumerate(totals)) {
                            // current choices and branch -> partial sum >= value
                            if (completed_node_data)
                                state.maybe_proof()->emit_proof_line("p " +
                                        to_string(ge_datas.at(x)->second.reverse_reif_line) + " " +
                                        to_string(completed_node_data->ges.at(x).forward_reif_line) + " +",
                                    ProofLevel::Temporary);
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_ge_states.at(x) + 1_i * not_choice + 1_i * ge_datas.at(x)->second.reif_flag >= 1_i,
                                ProofLevel::Temporary);
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * ge_datas.at(x)->second.reif_flag >= 1_i,
                                ProofLevel::Temporary);

                            // current choices and branch -> partial sum <= value
                            if (completed_node_data)
                                state.maybe_proof()->emit_proof_line("p " +
                                        to_string(le_datas.at(x)->second.reverse_reif_line) + " " +
                                        to_string(completed_node_data->les.at(x).forward_reif_line) + " +",
                                    ProofLevel::Temporary);
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_le_states.at(x) + 1_i * not_choice + 1_i * le_datas.at(x)->second.reif_flag >= 1_i,
                                ProofLevel::Temporary);
                            state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * le_datas.at(x)->second.reif_flag >= 1_i,
                                ProofLevel::Temporary);
                        }

                        // current choices and branch -> current state
                        state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice + 1_i * node_data->second->reif_flag >= 1_i,
                            ProofLevel::Temporary);

                        // because everything is non-negative, we can eliminate states where the
                        // partial sum is already too large.
                        bool eliminated = false;
                        for (const auto & [x, _] : enumerate(totals)) {
                            if (committed.at(x) + new_sums.at(x) > bounds.at(x).second) {
                                auto weight_var_str = prepare_and_get_bound_p_term(state, totals.at(x), true);
                                state.maybe_proof()->emit_proof_line("p " + to_string(ge_datas.at(x)->second.forward_reif_line) + " " +
                                        to_string(opb_lines->at(x).first) + " + " + weight_var_str + " +",
                                    ProofLevel::Temporary);
                                state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_ge_states.at(x) + 1_i * not_choice >= 1_i,
                                    ProofLevel::Temporary);
                                state.maybe_proof()->emit_rup_proof_line(trail + 1_i * not_in_full_state + 1_i * not_choice >= 1_i,
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
                            feasible_node_flags.push_back(node_data->second->reif_flag);
                            supported_values.emplace(val);
                        }
                    }
                });

                if constexpr (doing_proof_) {
                    // we must select at least one feasible choice from this variable's values
                    WeightedPseudoBooleanSum must_pick_one = trail + 1_i * not_in_full_state;
                    WeightedPseudoBooleanSum must_pick_one_val = must_pick_one, must_pick_one_node = must_pick_one;

                    for (auto & f : feasible_choices)
                        must_pick_one_val += 1_i * (all_vars.at(var_idx) == f);
                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_val >= 1_i, ProofLevel::Temporary);

                    for (const auto & [x, _] : enumerate(totals)) {
                        auto must_pick_one_le = must_pick_one, must_pick_one_ge = must_pick_one;
                        for (auto & f : feasible_le_flags.at(x))
                            must_pick_one_le += 1_i * f;
                        for (auto & f : feasible_ge_flags.at(x))
                            must_pick_one_ge += 1_i * f;
                        state.maybe_proof()->emit_rup_proof_line(must_pick_one_le >= 1_i, ProofLevel::Temporary);
                        state.maybe_proof()->emit_rup_proof_line(must_pick_one_ge >= 1_i, ProofLevel::Temporary);
                    }

                    for (auto & f : feasible_node_flags)
                        must_pick_one_node += 1_i * f;
                    state.maybe_proof()->emit_rup_proof_line(must_pick_one_node >= 1_i, ProofLevel::Temporary);
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
                state.maybe_proof()->emit_proof_comment("select from feasible choices for layer");
                WeightedPseudoBooleanSum must_pick_one = trail;
                for (auto & [_, data] : growing_layer_nodes)
                    must_pick_one += 1_i * data->reif_flag;
                state.maybe_proof()->emit_rup_proof_line(must_pick_one >= 1_i, ProofLevel::Temporary);
            }

            // we might have some values that never allowed a state to be created
            state.for_each_value(all_vars.at(var_idx), [&](Integer val) {
                    if (! supported_values.contains(val)) {
                        if constexpr (doing_proof_) {
                            state.maybe_proof()->emit_proof_comment("unsupported value on forward pass");
                            for (auto & [_, data] : growing_layer_nodes) {
                                state.maybe_proof()->emit_rup_proof_line(
                                        WeightedPseudoBooleanSum{} + 1_i * ! data->reif_flag + 1_i * (all_vars.at(var_idx) != val) >= 1_i,
                                        ProofLevel::Temporary);
                            }
                        }
                        increase_inference_to(inference, state.infer(all_vars.at(var_idx) != val, JustifyUsingRUP{}));
                        if (Inference::Contradiction == inference)
                            return;
                    }
                    });

            if (Inference::Contradiction == inference)
                return inference;

            completed_layer_nodes = move(growing_layer_nodes);
        }

        // states where the sum is too large are already gone, but we might
        // have remaining states where the final sum is too small.
        for (auto final_states_iter = completed_layer_nodes.begin(), final_states_iter_end = completed_layer_nodes.end(); final_states_iter != final_states_iter_end;) {
            bool eliminated = false;
            for (const auto & [x, _] : enumerate(totals)) {
                if (committed.at(x) + final_states_iter->first.at(x) < bounds.at(x).first) {
                    if constexpr (doing_proof_) {
                        auto weight_var_str = prepare_and_get_bound_p_term(state, totals.at(x), false);
                        state.maybe_proof()->emit_proof_line("p " + to_string(final_states_iter->second->les.at(x).forward_reif_line) +
                                " " + to_string(opb_lines->at(x).second) + " + " + weight_var_str + " +",
                            ProofLevel::Temporary);
                        state.maybe_proof()->emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * ! final_states_iter->second->les.at(x).reif_flag >= 1_i,
                            ProofLevel::Temporary);
                        state.maybe_proof()->emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * ! final_states_iter->second->reif_flag >= 1_i,
                            ProofLevel::Temporary);
                    }
                    completed_layer_nodes.erase(final_states_iter++);
                    eliminated = true;
                    break;
                }
            }

            if (! eliminated)
                ++final_states_iter;
        }

        if (completed_layer_nodes.empty()) {
            if constexpr (doing_proof_) {
                state.maybe_proof()->emit_proof_comment("no feasible choices remaining");
                state.maybe_proof()->emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} >= 1_i, ProofLevel::Temporary);
            }

            increase_inference_to(inference, state.infer(FalseLiteral{}, JustifyUsingRUP{}));
        }
        else {
            vector<Literal> inferences;
            for (const auto & [the_x, _] : enumerate(totals)) {
                auto x = the_x; // clang
                auto [lowest_iter, highest_iter] = minmax_element(completed_layer_nodes.begin(), completed_layer_nodes.end(),
                    [&](const pair<vector<Integer>, optional<FullNodeData>> & a,
                        const pair<vector<Integer>, optional<FullNodeData>> & b) { return a.first.at(x) < b.first.at(x); });

                auto lowest = lowest_iter->first.at(x);
                inferences.emplace_back(totals.at(x) >= committed.at(x) + lowest);

                auto highest = highest_iter->first.at(x);
                inferences.emplace_back(totals.at(x) < committed.at(x) + highest + 1_i);

                if constexpr (doing_proof_) {
                    state.maybe_proof()->emit_proof_comment("select from feasible terminal states");
                    for (auto & [_, data] : completed_layer_nodes) {
                        if (! data.has_value())
                            continue;

                        auto no_support_ge = trail + 1_i * ! data->ges.at(x).reif_flag;
                        state.maybe_proof()->emit_proof_line("p " + to_string(opb_lines->at(x).first) + " " + to_string(data->ges.at(x).forward_reif_line) + " +",
                            ProofLevel::Temporary);
                        state.maybe_proof()->emit_rup_proof_line(no_support_ge + 1_i * (totals.at(x) >= committed.at(x) + lowest) >= 1_i,
                            ProofLevel::Temporary);

                        auto no_support_le = trail + 1_i * ! data->les.at(x).reif_flag;
                        state.maybe_proof()->emit_proof_line("p " + to_string(opb_lines->at(x).second) + " " + to_string(data->les.at(x).forward_reif_line) + " +",
                            ProofLevel::Temporary);
                        state.maybe_proof()->emit_rup_proof_line(no_support_le + 1_i * (totals.at(x) < 1_i + committed.at(x) + highest) >= 1_i,
                            ProofLevel::Temporary);
                    }

                    state.maybe_proof()->emit_proof_comment("deduce overall conclusions");
                    state.maybe_proof()->emit_rup_proof_line(trail + 1_i * (totals.at(x) >= committed.at(x) + lowest) >= 1_i,
                        ProofLevel::Temporary);
                    state.maybe_proof()->emit_rup_proof_line(trail + 1_i * (totals.at(x) < 1_i + committed.at(x) + highest) >= 1_i,
                        ProofLevel::Temporary);
                }
            }

            increase_inference_to(inference, state.infer_all(inferences, JustifyUsingRUP{}));
        }

        return inference;
    }

    auto knapsack(
        State & state,
        const vector<vector<Integer>> & coeffs,
        const vector<IntegerVariableID> & vars,
        const vector<IntegerVariableID> & totals,
        const vector<pair<ProofLine, ProofLine>> & eqn_lines) -> pair<Inference, PropagatorState>
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

        auto inference = Inference::NoChange;

        if (undetermined_vars.empty()) {
            for (const auto & [x, t] : enumerate(totals)) {
                increase_inference_to(inference, state.infer(totals.at(x) == committed_sums.at(x), NoJustificationNeeded{}));
                if (Inference::Contradiction == inference)
                    return pair{inference, PropagatorState::DisableUntilBacktrack};
            }
        }

        for (const auto & [x, v] : enumerate(totals)) {
            increase_inference_to(inference, state.infer(v >= committed_sums.at(x), NoJustificationNeeded{}));
            if (Inference::Contradiction == inference)
                return pair{inference, PropagatorState::DisableUntilBacktrack};
        }

        vector<pair<Integer, Integer>> boundses;
        for (auto & t : totals)
            boundses.emplace_back(state.bounds(t));

        int temporary_proof_level = 0;
        if (state.maybe_proof())
            temporary_proof_level = state.maybe_proof()->temporary_proof_level();

        if (state.maybe_proof())
            increase_inference_to(inference, knapsack_bc<true>(state, committed_sums, boundses, coeffs, totals, vars, undetermined_vars, eqn_lines));
        else
            increase_inference_to(inference, knapsack_bc<false>(state, committed_sums, boundses, coeffs, totals, vars, undetermined_vars, nullopt));

        if (state.maybe_proof())
            state.maybe_proof()->forget_proof_level(temporary_proof_level);

        return pair{inference, PropagatorState::Enable};
    }
}

auto Knapsack::install(Propagators & propagators, State & initial_state) && -> void
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
    if (propagators.want_definitions()) {
        for (const auto & [cc_idx, cc] : enumerate(_coeffs)) {
            WeightedPseudoBooleanSum sum_eq;
            for (const auto & [idx, v] : enumerate(_vars))
                sum_eq += cc.at(idx) * v;
            auto [eq1, eq2] = propagators.define(initial_state, sum_eq == 1_i * _totals.at(cc_idx));
            eqns_lines.emplace_back(eq1.value(), eq2.value());
        }
    }

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};
    triggers.on_change.insert(triggers.on_change.end(), _totals.begin(), _totals.end());

    propagators.install(
        [coeffs = move(_coeffs), vars = move(_vars), totals = move(_totals), eqns_lines = move(eqns_lines)](State & state) -> pair<Inference, PropagatorState> {
            return knapsack(state, coeffs, vars, totals, eqns_lines);
        },
        triggers, "knapsack");
}

auto Knapsack::describe_for_proof() -> string
{
    return "knapsack";
}
