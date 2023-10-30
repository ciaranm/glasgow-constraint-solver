#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/innards/propagators.hh>
#include <iostream>
#include <list>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using std::cmp_equal;
using std::cmp_less;
using std::cmp_less_equal;
using std::cmp_not_equal;
using std::cout;
using std::get;
using std::list;
using std::make_pair;
using std::map;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

namespace
{
    auto select_root() -> long
    {
        // Might have better root selection in future
        // e.g. random
        return 0;
    }

    auto pos_min(const long a, const long b)
    {
        // Take the min of a and b, unless one of them is -1 (representing undefined)
        if (b == -1)
            return a;
        else if (a == -1)
            return b;
        else
            return min(a, b);
    }

    auto create_shifted_pos(long i, long j, ShiftedPosDataMaps & flag_data,
        const PosVarDataMap & pos_var_data, map<long, set<long>> & used_shifted_pos_values, State & state, const long root, const long n)
    {
        used_shifted_pos_values[i].insert(j);

        auto maybe_create_and_emplace_flag_data =
            [&](ProofFlagDataMap & flag_data, const long i, const long j, const WeightedPseudoBooleanLessEqual & definition, const string & name) {
                if (! flag_data[i].count(j)) {
                    auto [flag, forwards_reif_line, backwards_reif_line] = state.maybe_proof()->create_proof_flag_reifying(definition, name, ProofLevel::Top);
                    flag_data[i][j] = ProofFlagData{flag, forwards_reif_line, backwards_reif_line, {}};
                }
            };

        // distance_at_least[i][j] <=> pos[i] - pos[root] >= j
        maybe_create_and_emplace_flag_data(flag_data.distance_at_least, i, j,
            WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(i).var + -1_i * pos_var_data.at(root).var >= Integer{j}, "d" + to_string(i) + "ge" + to_string(j));

        // distance_at_least[i][j+1] <=> pos[i] - pos[root] >= j+1
        maybe_create_and_emplace_flag_data(flag_data.distance_at_least, i, j + 1,
            WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(i).var + -1_i * pos_var_data.at(root).var >= Integer{j + 1}, "d" + to_string(i) + "ge" + to_string(j + 1));

        // distance_at_least[i][j-n].term <=> pos[i] - pos[root] >= j-n
        maybe_create_and_emplace_flag_data(flag_data.distance_at_least, i, j - n,
            WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(i).var + -1_i * pos_var_data.at(root).var >= Integer{j - n}, "d" + to_string(i) + "gem" + to_string(n - j));

        // distance_at_least[i][j+1-n].term <=> pos[i] - pos[root] >= j+1-n
        maybe_create_and_emplace_flag_data(flag_data.distance_at_least, i, j + 1 - n,
            WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(i).var + -1_i * pos_var_data.at(root).var >= Integer{j + 1 - n}, "d" + to_string(i) + "gem" + to_string(n - j - 1));

        // distance[i][j] <=> distance_at_least[i][j] /\ not distance_at_least[i][j+1]
        maybe_create_and_emplace_flag_data(flag_data.distance, i, j,
            WeightedPseudoBooleanSum{} + 1_i * flag_data.distance_at_least[i][j].flag + -1_i * flag_data.distance_at_least[i][j + 1].flag >= 1_i, "d" + to_string(i) + "eq" + to_string(j));

        // distance[i][j-n] <=> distance_at_least[i][j-n] /\ not distance_at_least[i][j-n + 1]
        maybe_create_and_emplace_flag_data(flag_data.distance, i, j - n,
            WeightedPseudoBooleanSum{} + 1_i * flag_data.distance_at_least[i][j - n].flag + -1_i * flag_data.distance_at_least[i][j - n + 1].flag >= 1_i, "d" + to_string(i) + "eqm" + to_string(n - j));

        // shifted_pos[i][j] <=> distance[i][j] \/ distance[i][j-n]
        maybe_create_and_emplace_flag_data(flag_data.shifted_pos, i, j,
            WeightedPseudoBooleanSum{} + 1_i * flag_data.distance[i][j - n].flag + 1_i * flag_data.distance[i][j].flag >= 1_i, "q" + to_string(i) + "eq" + to_string(j));
    }

    auto prove_not_both(long i, long l, long k, ShiftedPosDataMaps & flag_data, const PosVarDataMap & pos_var_data,
        const bool using_shifted_pos, const long & n, State & state) -> ProofLine
    {
        ProofLine neq_line{};

        if (using_shifted_pos) {
            auto & shifted_pos = flag_data.shifted_pos;
            auto & distance_at_least = flag_data.distance_at_least;
            auto & distance = flag_data.distance;

            if (shifted_pos[i][l].neq_lines.contains(k)) {
                // Don't reprove this if we did it before
                return shifted_pos[i][l].neq_lines[k];
            }

            state.infer_true(JustifyExplicitly{
                [&](Proof & proof) {
                    // proof.emit_proof_comment("************** " + to_string(i) + ", " + to_string(l) + ", " + to_string(k) + " ******************");
                    stringstream proofline;
                    proofline
                        << " p " << distance_at_least[i][l + 1].backwards_reif_line
                        << " " << distance_at_least[i][k].forwards_reif_line << " + s";
                    proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                    proofline.str("");
                    proofline << " p " << distance_at_least[i][l].forwards_reif_line
                              << " " << distance_at_least[i][k - n + 1].backwards_reif_line << " + s";
                    proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                    proofline.str("");
                    proofline << " p " << distance_at_least[i][l - n + 1].backwards_reif_line
                              << " " << distance_at_least[i][k - n].forwards_reif_line << " + s";
                    proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                    proofline.str("");
                    proofline << " p " << distance_at_least[i][l - n + 1].backwards_reif_line
                              << " " << distance_at_least[i][k].forwards_reif_line << " + s";
                    proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                    proof.emit_rup_proof_line(
                        WeightedPseudoBooleanSum{} + 1_i * ! shifted_pos[i][k].flag + 1_i * ! distance[i][l].flag >= 1_i, ProofLevel::Temporary);

                    proof.emit_proof_comment("NEQ");
                    neq_line = proof.emit_rup_proof_line(
                        WeightedPseudoBooleanSum{} + 1_i * ! shifted_pos[i][k].flag + 1_i * ! shifted_pos[i][l].flag >= 1_i, ProofLevel::Top);
                }});

            shifted_pos[i][l].neq_lines[k] = neq_line;
        }
        else {
            auto & shifted_pos = flag_data.shifted_pos;
            if (shifted_pos[i][l].neq_lines.contains(k)) {
                // Don't reprove this if we did it before
                return shifted_pos[i][l].neq_lines[k];
            }
            state.infer_true(JustifyExplicitly{
                [&](Proof & proof) {
                    proof.emit_proof_comment("NEQ");
                    neq_line = proof.emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(i).var != Integer{k}) + 1_i * (pos_var_data.at(i).var != Integer{l}) >= 1_i, ProofLevel::Top);
                }});

            shifted_pos[i][l].neq_lines[k] = neq_line;
        }
        return neq_line;
    }

    auto prove_unreachable(
        State & state,
        const vector<IntegerVariableID> & succ,
        const long & root,
        const PosVarDataMap & pos_var_data,
        const ConstraintStateHandle & proof_flag_data_handle,
        const bool using_dominance,
        const Literal & assumption = TrueLiteral{})
    {
        const auto using_shifted_pos = ! using_dominance && root != 0;
        auto n = static_cast<long>(succ.size());
        map<long, set<long>> used_pos_vals{};

        auto & data_maps_for_each_root = any_cast<map<long, ShiftedPosDataMaps> &>(
            state.get_persistent_constraint_state(proof_flag_data_handle));

        ShiftedPosDataMaps flag_data{};
        if (data_maps_for_each_root.count(root) != 0) {
            // Retrieved cached versions if we've started from this root before
            flag_data = data_maps_for_each_root[root];
        }

        ProofLine last_al1_pos_line{};
        // Prove pos[root] = 0
        if (using_dominance) {
            // TODO:
        }
        else if (using_shifted_pos) {
            create_shifted_pos(root, 0, flag_data, pos_var_data, used_pos_vals, state, root, n);

            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                proof.emit_proof_comment("AL1 position");
                last_al1_pos_line = proof.emit_rup_proof_line(
                    WeightedPseudoBooleanSum{} + 1_i * flag_data.shifted_pos[root][0].flag >= 1_i,
                    ProofLevel::Current);
            }});
        }
        else {
            used_pos_vals[0].insert(0);
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                proof.emit_proof_comment("AL1 position");
                last_al1_pos_line = proof.emit_rup_proof_line(
                    WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(root).var == 0_i) >= 1_i,
                    ProofLevel::Current);
            }});
        }

        vector<ProofLine> al1_pos_lines = {last_al1_pos_line};

        auto skip_based_on_assumption = [&](IntegerVariableID var, Integer val, Literal assumption) -> bool {
            return overloaded{
                [&](TrueLiteral) {
                    return false;
                },
                [&](FalseLiteral) {
                    return false;
                },
                [&](IntegerVariableCondition cond) {
                    if (cond.var == var) {
                        if ((cond.op == VariableConditionOperator::Equal && val != cond.value) ||
                            (cond.op == VariableConditionOperator::NotEqual && val == cond.value)) {
                            return true;
                        }
                        else if (cond.op == VariableConditionOperator::GreaterEqual || cond.op == VariableConditionOperator::Less) {
                            throw UnexpectedException{"Comparison assumptions not supported for reachability proof."};
                        }
                        else {
                            return false;
                        }
                    }
                    else {
                        if (cond.op == VariableConditionOperator::Equal && val == cond.value) {
                            return true;
                        }
                        else if (cond.op == VariableConditionOperator::GreaterEqual || cond.op == VariableConditionOperator::Less) {
                            throw UnexpectedException{"Comparison assumptions not supported for reachability proof."};
                        }
                        else {
                            return false;
                        }
                    }
                }}
                .visit(assumption);
        };

        long count = 1;
        set<long> all_reached_nodes = {root};
        set<long> last_reached_nodes = {root};

        while (cmp_less_equal(count, all_reached_nodes.size())) {
            set<long> new_reached_nodes{};
            vector<ProofLine> last_pos_implies_lines = {};

            for (const auto & node : last_reached_nodes) {
                WeightedPseudoBooleanSum possible_successor_sum{};
                vector<ProofLine> successor_implies_lines{};

                // For each possible successor
                state.for_each_value(succ[node], [&](Integer val) {
                    if (skip_based_on_assumption(succ[node], val, assumption)) return;
                    possible_successor_sum += 1_i * (succ[node] == val);
                    auto next_node = val.raw_value;
                    new_reached_nodes.insert(next_node);

                    // successor_implies_lines += Prove pos[node][count - 1] /\ succ[node] = next_node => pos[next_node][count]
                    if (using_shifted_pos) {
                        // Have to account for when we circle back round to 0 and the count and count-n swap roles
                        long next_distance = count;
                        long next_distance_mod = count - n;
                        if (next_node == 0) {
                            next_distance = count - n;
                            next_distance_mod = count;
                        }

                        create_shifted_pos(next_node, count, flag_data, pos_var_data, used_pos_vals, state, root, n);

                        state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                            // Add to get succ[node]==next_node /\ distance_at_least[node][count - 1] => distance_at_least[next_node][count]
                            stringstream proofline;
                            proofline << "p ";
                            proofline << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " ";
                            proofline << flag_data.distance_at_least[node][count - 1].forwards_reif_line << " + ";
                            proofline << flag_data.distance_at_least[next_node][next_distance].backwards_reif_line << " + s";
                            auto last_proof_line = proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                            // Further add to get succ[node]==next_node /\ distance_at_least[node][count - 1] /\ !distance_at_least[node][count] =>
                            // distance_at_least[next_node][count] /\ !distance_at_Least[next_node][count + 1]
                            proofline.str("");
                            proofline << "p ";
                            proofline << pos_var_data.at(node).plus_one_lines.at(next_node).leq_line << " ";
                            proofline << flag_data.distance_at_least[node][count].backwards_reif_line << " + ";
                            proofline << flag_data.distance_at_least[next_node][next_distance + 1].forwards_reif_line << " + s ";
                            proofline << last_proof_line << " + ";
                            proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                            // Now we can RUP succ[node]==next_node /\ distance[next_node][count] => distance[next_node][count + 1]
                            proof.emit_rup_proof_line_under_trail(state,
                                WeightedPseudoBooleanSum{} +
                                        1_i * flag_data.distance[next_node][next_distance].flag + 1_i * (succ[node] != val) +
                                        1_i * (! flag_data.distance[node][count - 1].flag) >=
                                    1_i,
                                ProofLevel::Temporary);

                            // Add to get succ[node]==next_node /\ distance_at_least[node][count - 1 -n] => distance_at_least[next_node][count -n]
                            proofline.str("");
                            proofline << "p ";
                            proofline << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " ";
                            proofline << flag_data.distance_at_least[node][count - 1 - n].forwards_reif_line << " + ";
                            proofline << flag_data.distance_at_least[next_node][next_distance_mod].backwards_reif_line << " + s";
                            last_proof_line = proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                            // Further add to get  succ[node]==next_node /\ distance_at_least[node][count - 1 - n] /\ !distance_at_least[node][count - n] =>
                            // distance_at_least[next_node][count - n] /\ !distance_at_Least[next_node][count + 1 - n]
                            proofline.str("");
                            proofline << "p ";
                            proofline << pos_var_data.at(node).plus_one_lines.at(next_node).leq_line << " ";
                            proofline << flag_data.distance_at_least[node][count - n].backwards_reif_line << " + ";
                            proofline << flag_data.distance_at_least[next_node][next_distance_mod + 1].forwards_reif_line << " + s ";
                            proofline << last_proof_line << " + ";

                            proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                            proof.emit_proof_comment("q" + to_string(node) + to_string(count - 1) + " implies q" + to_string(next_node) + to_string(count));
                            // RUP shifted_pos[node][count-1] /\ succ[node] = next_node => shifted_pos[next_node][i]
                            successor_implies_lines.emplace_back(proof.emit_rup_proof_line_under_trail(state,
                                WeightedPseudoBooleanSum{} + 1_i * flag_data.shifted_pos[next_node][count].flag + 1_i * (succ[node] != val) +
                                        1_i * (! flag_data.shifted_pos[node][count - 1].flag) >=
                                    1_i,
                                ProofLevel::Current));
                        }});
                    }
                    else {
                        // Not using shifted pos, just use the actual pos values

                        used_pos_vals[next_node].insert(count);
                        state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                            // succ[node] == next_node /\ pos[node] == count - 1 => pos[next_node] == count
                            successor_implies_lines.emplace_back(proof.emit_rup_proof_line(
                                WeightedPseudoBooleanSum{} + 1_i * (pos_var_data.at(node).var != Integer{count - 1}) +
                                        1_i * (succ[node] != val) + 1_i * (pos_var_data.at(next_node).var == Integer{count}) >=
                                    1_i,
                                ProofLevel::Current));
                        }});
                    }
                });

                // last_pos_implies_lines += Prove pos[node][count - 1] => \/_{next_node} pos[next_node][count]
                state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                    proof.emit_proof_comment("Some value:");
                    auto al1_x_line = proof.emit_rup_proof_line_under_trail(state,
                        possible_successor_sum + 1_i * ! assumption >= 1_i, ProofLevel::Temporary);

                    stringstream proofline;
                    proofline << "p ";
                    proofline << al1_x_line << " ";
                    for (const auto & l : successor_implies_lines) {
                        proofline << l << " + s ";
                    }
                    last_pos_implies_lines.emplace_back(proof.emit_proof_line(proofline.str(), ProofLevel::Current));
                }});
            }

            // Prove \/_{next_node} pos[next_node][count]
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                stringstream proofline;
                proofline << "p ";
                proofline << last_al1_pos_line << " ";
                for (const auto & l : last_pos_implies_lines) {
                    proofline << l << " + s ";
                }
                proof.emit_proof_comment("AL1 position");
                al1_pos_lines.emplace_back(proof.emit_proof_line(proofline.str(), ProofLevel::Current));
                last_al1_pos_line = al1_pos_lines.back();
            }});

            last_reached_nodes = new_reached_nodes;

            // Continue until we've logged more layers than we have reached nodes (Hall violator)
            all_reached_nodes.insert(new_reached_nodes.begin(), new_reached_nodes.end());
            count++;
        }

        vector<ProofLine> am1_pos_lines{};

        // Prove at most one pos[node][count] for each count
        // In order to actually get the contradiction we need to retrieve the at_least_1_constraints
        // and in order to do that we need a clique of not-equals over the vars
        state.infer_true(JustifyExplicitly{
            [&](Proof & proof) {
                for (const auto & i : all_reached_nodes) {
                    stringstream proofline;
                    if (used_pos_vals[i].size() > 1) {
                        auto k = ++used_pos_vals[i].begin();
                        auto l = used_pos_vals[i].begin();
                        proofline << "p " << prove_not_both(i, (*l), (*k), flag_data, pos_var_data, using_shifted_pos, n, state);
                        vector<ProofLine> neq_lines{};
                        k++;
                        auto k_count = 2;
                        while (k != used_pos_vals[i].end()) {
                            proofline << " " << k_count << " * ";
                            l = used_pos_vals[i].begin();
                            while (l != k) {
                                proofline << prove_not_both(i, (*l), (*k), flag_data, pos_var_data, using_shifted_pos, n, state) << " + ";
                                l++;
                            }
                            proofline << k_count + 1 << " d ";
                            k++;
                            k_count++;
                        }
                        proof.emit_proof_comment("AM1");
                        am1_pos_lines.emplace_back(proof.emit_proof_line(proofline.str(), ProofLevel::Current));
                    }
                    else if (used_pos_vals[i].size() == 1) {
                        auto idx = *used_pos_vals[i].begin();
                        proof.emit_proof_comment("AM1");
                        am1_pos_lines.emplace_back(proof.emit_rup_proof_line(
                            WeightedPseudoBooleanSum{} + 1_i * ! assumption + 1_i * ! (flag_data.shifted_pos[i][idx].flag) >= 0_i,
                            ProofLevel::Current));
                    }
                }
            }});

        // Add together AL1 and AM1 lines for contradiction
        state.infer_true(JustifyExplicitly{
            [&](Proof & proof) {
                stringstream proofline;
                proofline << "p ";
                proofline << al1_pos_lines[0] << " ";

                for (auto it = al1_pos_lines.begin() + 1; it < al1_pos_lines.end(); it++) {
                    proofline << *it << " + ";
                }

                for (auto it = am1_pos_lines.begin(); it < am1_pos_lines.end(); it++) {
                    proofline << *it << " + ";
                }

                proofline << " s";
                proof.emit_proof_line(proofline.str(), ProofLevel::Current);
            }});

        // Update cache
        data_maps_for_each_root[root] = flag_data;
    }

    auto explore(
        const long & node,
        long & count,
        vector<long> & lowlink,
        vector<long> & visit_number,
        long & start_prev_subtree,
        long & end_prev_subtree,
        long & prev_subroot,
        long & root,
        const vector<IntegerVariableID> & succ,
        const SCCOptions & scc_options,
        const PosVarDataMap & pos_var_data,
        const ConstraintStateHandle & proof_flag_data_handle,
        State & state) -> pair<Inference, vector<pair<long, long>>>
    {
        visit_number[node] = count;
        lowlink[node] = count;
        count++;

        Inference result = gcs::innards::Inference::NoChange;
        vector<pair<long, long>> back_edges{};
        state.for_each_value_while(succ[node], [&](Integer w) -> bool {
            if (visit_number[w.raw_value] == -1) {
                auto explore_result = explore(w.raw_value, count, lowlink, visit_number, start_prev_subtree, end_prev_subtree,
                    prev_subroot, root, succ, scc_options, pos_var_data, proof_flag_data_handle, state);
                increase_inference_to(result, explore_result.first);
                if (result == Inference::Contradiction) {
                    return false;
                }
                auto w_back_edges = explore_result.second;
                back_edges.insert(back_edges.end(), w_back_edges.begin(), w_back_edges.end());
                lowlink[node] = pos_min(lowlink[node], lowlink[w.raw_value]);
            }
            else {
                if (visit_number[w.raw_value] >= start_prev_subtree && visit_number[w.raw_value] <= end_prev_subtree) {
                    back_edges.emplace_back(node, w.raw_value);
                }
                else if (scc_options.prune_skip && visit_number[w.raw_value] < start_prev_subtree) {
                    state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                        proof.emit_proof_comment("Pruning edge (" + to_string(node) + "," + to_string(w.raw_value) + ")" + " that would skip subtree");
                        prove_unreachable(state, succ, prev_subroot, pos_var_data, proof_flag_data_handle, false, succ[node] == w);
                    }});

                    increase_inference_to(result, state.infer(succ[node] != w, NoJustificationNeeded{}));
                }
                lowlink[node] = pos_min(lowlink[node], visit_number[w.raw_value]);
            }

            return true;
        });

        if (result == Inference::Contradiction) {
            // Shortcut if we contradicted at a deeper layer, trying to prove contradiction again will cause problems.
            return make_pair(result, back_edges);
        }

        if (lowlink[node] == visit_number[node]) {
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                proof.emit_proof_comment("More than one SCC");
                if (node == root) {
                    int unreachable_node = 0;
                    while (visit_number[unreachable_node] != -1) {
                        unreachable_node++;
                    }
                    prove_unreachable(state, succ, unreachable_node, pos_var_data, proof_flag_data_handle, scc_options.prove_using_dominance);
                }
                else {
                    prove_unreachable(state, succ, node, pos_var_data, proof_flag_data_handle, scc_options.prove_using_dominance);
                }
            }});
            return make_pair(Inference::Contradiction, back_edges);
        }
        else
            return make_pair(result, back_edges);
    }

    auto check_sccs(const vector<IntegerVariableID> & succ, const SCCOptions & scc_options, const PosVarDataMap & pos_var_data, const ConstraintStateHandle & proof_flag_data_handle, State & state) -> Inference
    {
        auto result = Inference::NoChange;
        auto root = select_root();
        long count = 1;
        long start_subtree = 0;
        long end_subtree = 0;
        long prev_subroot = root;
        vector<long> lowlink = vector<long>(succ.size(), -1);
        vector<long> visit_number = vector<long>(succ.size(), -1);
        lowlink[root] = 0;
        visit_number[root] = 0;

        state.for_each_value_while(succ[root], [&](Integer v) -> bool {
            if (visit_number[v.raw_value] == -1) {
                auto explore_result = explore(v.raw_value, count, lowlink, visit_number, start_subtree,
                    end_subtree, prev_subroot, root, succ, scc_options, pos_var_data, proof_flag_data_handle, state);
                increase_inference_to(result, explore_result.first);
                if (result == Inference::Contradiction) {
                    return false;
                }
                auto back_edges = explore_result.second;

                if (back_edges.empty()) {
                    state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                        proof.emit_proof_comment("No back edges:");
                        prove_unreachable(state, succ, prev_subroot, pos_var_data, proof_flag_data_handle, scc_options.prove_using_dominance);
                    }});

                    increase_inference_to(result, Inference::Contradiction);
                    return false;
                }
                else if (scc_options.fix_req && back_edges.size() == 1) {

                    state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                        proof.emit_proof_comment("Fix required back edge (" + to_string(back_edges[0].first) + ", " + to_string(back_edges[0].second) + "):");
                        prove_unreachable(state, succ, back_edges[0].first, pos_var_data, proof_flag_data_handle, scc_options.prove_using_dominance, succ[back_edges[0].first] != Integer{back_edges[0].second});
                    }});

                    increase_inference_to(result, state.infer(succ[back_edges[0].first] == Integer{back_edges[0].second}, NoJustificationNeeded{}));
                }
                start_subtree = end_subtree + 1;
                end_subtree = count - 1;
                prev_subroot = v.raw_value;
            }
            return true;
        });

        if (cmp_not_equal(count, succ.size()) && result != Inference::Contradiction) {
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                proof.emit_proof_comment("Disconnected graph:");
                prove_unreachable(state, succ, root, pos_var_data, proof_flag_data_handle, scc_options.prove_using_dominance);
            }});

            return Inference::Contradiction;
        }

        if (scc_options.prune_root && start_subtree > 1) {
            state.for_each_value_while(succ[root], [&](Integer v) -> bool {
                if (visit_number[v.raw_value] < start_subtree) {
                    state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                        proof.emit_proof_comment("Prune impossible edges from root node:");
                        prove_unreachable(state, succ, root, pos_var_data, proof_flag_data_handle, scc_options.prove_using_dominance, succ[root] == v);
                    }});

                    increase_inference_to(result, state.infer(succ[root] != v, JustifyUsingRUP{}));
                }

                return true;
            });
        }

        return result;
    }

    auto propagate_circuit_using_scc(const vector<IntegerVariableID> & succ,
        const SCCOptions & scc_options,
        const PosVarDataMap & pos_var_data,
        const ConstraintStateHandle & proof_flag_data_handle,
        const ConstraintStateHandle & unassigned_handle,
        State & state)
        -> Inference
    {
        auto result = propagate_non_gac_alldifferent(unassigned_handle, state);
        if (result == Inference::Contradiction) return result;
        increase_inference_to(result, check_sccs(succ, scc_options, pos_var_data, proof_flag_data_handle, state));
        if (result == Inference::Contradiction) return result;
        increase_inference_to(result, prevent_small_cycles(succ, pos_var_data, unassigned_handle, state));
        return result;
    }
}

CircuitSCC::CircuitSCC(std::vector<IntegerVariableID> var, bool gacAllDifferent, const SCCOptions s) :
    CircuitBase(std::move(var), gacAllDifferent),
    scc_options(s)
{
}

auto CircuitSCC::clone() const -> unique_ptr<Constraint>
{
    return make_unique<CircuitSCC>(_succ, _gac_all_different, scc_options);
}

auto CircuitSCC::install(Propagators & propagators, State & initial_state) && -> void
{
    auto pos_var_data = CircuitBase::set_up(propagators, initial_state);

    // Keep track of unassigned vars
    list<IntegerVariableID> unassigned{};
    for (auto v : _succ) {
        unassigned.emplace_back(v);
    }
    auto unassigned_handle = initial_state.add_constraint_state(unassigned);

    auto proof_flag_data_handle = initial_state.add_persistent_constraint_state(map<long, ShiftedPosDataMaps>{});

    Triggers triggers;
    triggers.on_change = {_succ.begin(), _succ.end()};
    propagators.install(
        [succ = _succ,
            pos_var_data = pos_var_data,
            proof_flag_data_handle = proof_flag_data_handle,
            unassigned_handle = unassigned_handle,
            options = scc_options](State & state) -> pair<Inference, PropagatorState> {
            auto result = propagate_circuit_using_scc(succ, options, pos_var_data, proof_flag_data_handle, unassigned_handle, state);
            return pair{result, PropagatorState::Enable};
        },
        triggers,
        "circuit");
}