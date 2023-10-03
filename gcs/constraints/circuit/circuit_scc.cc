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

    auto create_shifted_pos(long i, long j, ProofFlagDataMap & distance_at_least, ProofFlagDataMap & distance, ProofFlagDataMap & shifted_pos,
        const PosVarDataMap & pos_var_data, State & state, const long root, const long n)
    {
        auto maybe_create_and_emplace_flag_data =
            [&](ProofFlagDataMap & flag_data, const long i, const long j, const WeightedPseudoBooleanLessEqual & definition, const string & name) {
                if (! flag_data[i].count(j)) {
                    auto [flag, forwards_reif_line, backwards_reif_line] = state.maybe_proof()->create_proof_flag_reifying(definition, name, ProofLevel::Current);
                    flag_data[i][j] = ProofFlagData{flag, forwards_reif_line, backwards_reif_line};
                }
            };

        // distance_at_least[i][j] <=> pos[i] - pos[root] >= j
        maybe_create_and_emplace_flag_data(distance_at_least, i, j,
            WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(i).var + -1_i * pos_var_data.at(root).var >= Integer{j}, "d" + to_string(i) + "ge" + to_string(j));

        // distance_at_least[i][j+1] <=> pos[i] - pos[root] >= j+1
        maybe_create_and_emplace_flag_data(distance_at_least, i, j + 1,
            WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(i).var + -1_i * pos_var_data.at(root).var >= Integer{j + 1}, "d" + to_string(i) + "ge" + to_string(j + 1));

        // distance_at_least[i][j-n].term <=> pos[i] - pos[root] >= j-n
        maybe_create_and_emplace_flag_data(distance_at_least, i, j - n,
            WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(i).var + -1_i * pos_var_data.at(root).var >= Integer{j - n}, "d" + to_string(i) + "gem" + to_string(n - j));

        // distance_at_least[i][j+1-n].term <=> pos[i] - pos[root] >= j+1-n
        maybe_create_and_emplace_flag_data(distance_at_least, i, j + 1 - n,
            WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(i).var + -1_i * pos_var_data.at(root).var >= Integer{j + 1 - n}, "d" + to_string(i) + "gem" + to_string(n - j - 1));

        // distance[i][j] <=> distance_at_least[i][j] /\ not distance_at_least[i][j+1]
        maybe_create_and_emplace_flag_data(distance, i, j,
            WeightedPseudoBooleanSum{} + 1_i * distance_at_least[i][j].flag + -1_i * distance_at_least[i][j + 1].flag >= 1_i, "d" + to_string(i) + "eq" + to_string(j));

        // distance[i][j-n] <=> distance_at_least[i][j-n] /\ not distance_at_least[i][j-n + 1]
        maybe_create_and_emplace_flag_data(distance, i, j - n,
            WeightedPseudoBooleanSum{} + 1_i * distance_at_least[i][j - n].flag + -1_i * distance_at_least[i][j - n + 1].flag >= 1_i, "d" + to_string(i) + "eqm" + to_string(n - j));

        // shifted_pos[i][j] <=> distance[i][j] \/ distance[i][j-n]
        maybe_create_and_emplace_flag_data(shifted_pos, i, j,
            WeightedPseudoBooleanSum{} + 1_i * distance[i][j - n].flag + 1_i * distance[i][j].flag >= 1_i, "q" + to_string(i) + "eq" + to_string(j));
    }

    auto prove_not_both(long i, long l, long k,
        ProofFlagDataMap & distance_at_least,
        ProofFlagDataMap & distance,
        ProofFlagDataMap & shifted_pos,
        const long & n, State & state) -> ProofLine
    {
        ProofLine neq_line;
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

                proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} + 1_i * ! shifted_pos[i][k].flag + 1_i * ! distance[i][l].flag >= 1_i, ProofLevel::Temporary);

                proof.emit_proof_comment("NEQ");
                neq_line = proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} + 1_i * ! shifted_pos[i][k].flag + 1_i * ! shifted_pos[i][l].flag >= 1_i, ProofLevel::Current);
            }});
        return neq_line;
    }

    auto prove_unreachable(State & state, const vector<IntegerVariableID> & succ, const long & root, PosVarDataMap pos_var_data, const Literal & assumption = TrueLiteral{})
    {
        auto n = static_cast<long>(succ.size());
        state.infer_true(JustifyExplicitly{[&](Proof & proof) {
            proof.emit_proof_comment("=== REACHABILITY PROOF ===");
        }});
        // distance_at_least[i][j] means pos[i] - pos[root] >= j
        ProofFlagDataMap distance_at_least;

        // distance[i][j] means pos[i] - pos[root] == j
        ProofFlagDataMap distance;

        // shifted_pos[i][j] means pos[i] - pos[root] = j mod n
        ProofFlagDataMap shifted_pos;

        create_shifted_pos(root, 0, distance_at_least, distance, shifted_pos, pos_var_data, state, root, n);
        vector<ProofLine> al1_q_lines;

        // Should be able to RUP shifted_pos[root][0] >= 1
        state.infer_true(JustifyExplicitly{[&](Proof & proof) {
            proof.emit_proof_comment("LAYER");
            al1_q_lines.emplace_back(proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * ! assumption + 1_i * shifted_pos[root][0].flag >= 1_i, ProofLevel::Current));
        }});

        // Now collect all the shifted_pos[i][1] for each possible i
        vector<ProofLine> next_node_implies_lines{};
        WeightedPseudoBooleanSum possible_successor_sum{};
        set<long> reached_nodes = {};

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

        state.for_each_value(succ[root], [&](Integer val) {
            if (skip_based_on_assumption(succ[root], val, assumption)) return;

            possible_successor_sum += 1_i * (succ[root] == val);
            auto next_node = val.raw_value;
            reached_nodes.insert(next_node);
            create_shifted_pos(next_node, 1, distance_at_least, distance, shifted_pos, pos_var_data, state, root, n);

            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                stringstream proofline;

                // Add to get succ[root] = next_node => distance_at_least[next_node][1]
                proofline << "p ";
                proofline << pos_var_data.at(root).plus_one_lines.at(next_node).geq_line << " ";
                proofline << distance_at_least[next_node][1].backwards_reif_line << " + s";
                proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                // Add to get succ[root] = next_node => !distance_at_least[next_node][2]
                proofline.str("");
                proofline << "p ";
                proofline << pos_var_data.at(root).plus_one_lines.at(next_node).leq_line << " ";
                proofline << distance_at_least[next_node][2].forwards_reif_line << " + s";

                // Now RUP succ[root] = next_node => shifted_pos[next_node][1]
                proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);
                next_node_implies_lines.emplace_back(proof.emit_rup_proof_line_under_trail(state,
                    WeightedPseudoBooleanSum{} + 1_i * ! assumption + 1_i * shifted_pos[next_node][1].flag + 1_i * (succ[root] != val) >= 1_i, ProofLevel::Current));
            }});
        });

        vector<ProofLine> am1_q_lines;
        ProofLine al1_q_line;
        // RUP that succ[root] takes some value
        // allows us to derive at least 1 shifted_pos[node][1]
        state.infer_true(JustifyExplicitly{[&](Proof & proof) {
            proof.emit_proof_comment("Some value:");
            auto al1_x_line = proof.emit_rup_proof_line_under_trail(state, possible_successor_sum + 1_i * ! assumption >= 1_i, ProofLevel::Temporary);
            stringstream proofline;
            proofline << "p ";
            proofline << al1_x_line << " ";
            for (const auto & l : next_node_implies_lines) {
                proofline << l << " + ";
            }
            proof.emit_proof_comment("LAYER");
            al1_q_lines.emplace_back(proof.emit_proof_line(proofline.str(), ProofLevel::Current));
            al1_q_line = al1_q_lines.back();
        }});

        int count = 2;
        auto all_reached_nodes = reached_nodes;

        all_reached_nodes.insert(root);

        while (cmp_less_equal(count, all_reached_nodes.size())) {
            set<long> new_reached_nodes{};
            vector<ProofLine> q_implies_lines = {};

            for (const auto & node : reached_nodes) {

                possible_successor_sum = {};
                next_node_implies_lines = {};
                state.for_each_value(succ[node], [&](Integer val) {
                    if (skip_based_on_assumption(succ[node], val, assumption)) return;
                    possible_successor_sum += 1_i * (succ[node] == val);
                    auto next_node = val.raw_value;
                    new_reached_nodes.insert(next_node);
                    create_shifted_pos(next_node, count, distance_at_least, distance, shifted_pos, pos_var_data, state, root, n);

                    // Have to account for when we circle back round to 0 and the count and count-n swap roles
                    long next_distance = count;
                    long next_distance_mod = count - n;
                    if (next_node == 0) {
                        next_distance = count - n;
                        next_distance_mod = count;
                    }
                    state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                        // Add to get succ[node]==next_node /\ distance_at_least[node][count - 1] => distance_at_least[next_node][count]
                        stringstream proofline;
                        proofline << "p ";
                        proofline << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " ";
                        proofline << distance_at_least[node][count - 1].forwards_reif_line << " + ";
                        proofline << distance_at_least[next_node][next_distance].backwards_reif_line << " + s";
                        auto last_proof_line = proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                        // Further add to get succ[node]==next_node /\ distance_at_least[node][count - 1] /\ !distance_at_least[node][count] =>
                        // distance_at_least[next_node][count] /\ !distance_at_Least[next_node][count + 1]
                        proofline.str("");
                        proofline << "p ";
                        proofline << pos_var_data.at(node).plus_one_lines.at(next_node).leq_line << " ";
                        proofline << distance_at_least[node][count].backwards_reif_line << " + ";
                        proofline << distance_at_least[next_node][next_distance + 1].forwards_reif_line << " + s ";
                        proofline << last_proof_line << " + ";
                        proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                        // Now we can RUP succ[node]==next_node /\ distance[next_node][count] => distance[next_node][count + 1]
                        proof.emit_rup_proof_line_under_trail(state,
                            WeightedPseudoBooleanSum{} + 1_i * distance[next_node][next_distance].flag + 1_i * (succ[node] != val) + 1_i * (! distance[node][count - 1].flag) >= 1_i, ProofLevel::Temporary);

                        // Add to get succ[node]==next_node /\ distance_at_least[node][count - 1 -n] => distance_at_least[next_node][count -n]
                        proofline.str("");
                        proofline << "p ";
                        proofline << pos_var_data.at(node).plus_one_lines.at(next_node).geq_line << " ";
                        proofline << distance_at_least[node][count - 1 - n].forwards_reif_line << " + ";
                        proofline << distance_at_least[next_node][next_distance_mod].backwards_reif_line << " + s";
                        last_proof_line = proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                        // Further add to get  succ[node]==next_node /\ distance_at_least[node][count - 1 - n] /\ !distance_at_least[node][count - n] =>
                        // distance_at_least[next_node][count - n] /\ !distance_at_Least[next_node][count + 1 - n]
                        proofline.str("");
                        proofline << "p ";
                        proofline << pos_var_data.at(node).plus_one_lines.at(next_node).leq_line << " ";
                        proofline << distance_at_least[node][count - n].backwards_reif_line << " + ";
                        proofline << distance_at_least[next_node][next_distance_mod + 1].forwards_reif_line << " + s ";
                        proofline << last_proof_line << " + ";
                        //                        proofline << distance[node][count - n - 1].forwards_reif_line << " + s";
                        proof.emit_proof_line(proofline.str(), ProofLevel::Temporary);

                        proof.emit_proof_comment("q" + to_string(node) + to_string(count - 1) + " implies q" + to_string(next_node) + to_string(count));
                        // RUP shifted_pos[node][i-1] /\ succ[node] = next_node => shifted_pos[next_node][i]
                        next_node_implies_lines.emplace_back(proof.emit_rup_proof_line_under_trail(state,
                            WeightedPseudoBooleanSum{} + 1_i * shifted_pos[next_node][count].flag + 1_i * (succ[node] != val) + 1_i * (! shifted_pos[node][count - 1].flag) >= 1_i, ProofLevel::Current));
                    }});
                });

                // RUP that succ[node] takes some value and then derive
                // shifted_pos[node][i-1] => \/_possible_successors shifted_pos[next_node][i]
                state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                    proof.emit_proof_comment("Some value:");
                    auto al1_x_line = proof.emit_rup_proof_line_under_trail(state, possible_successor_sum + 1_i * ! assumption >= 1_i, ProofLevel::Temporary);

                    stringstream proofline;
                    proofline << "p ";
                    proofline << al1_x_line << " ";
                    for (const auto & l : next_node_implies_lines) {
                        proofline << l << " + s ";
                    }
                    q_implies_lines.emplace_back(proof.emit_proof_line(proofline.str(), ProofLevel::Current));
                }});
            }

            // Finally, this allows us to rup at least 1 shifted_pos[node][k] for k in reached nodes
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                stringstream proofline;
                proofline << "p ";
                proofline << al1_q_line << " ";
                for (const auto & l : q_implies_lines) {
                    proofline << l << " + s ";
                }
                proof.emit_proof_comment("LAYER");
                al1_q_lines.emplace_back(proof.emit_proof_line(proofline.str(), ProofLevel::Current));
                al1_q_line = al1_q_lines.back();
            }});

            reached_nodes = new_reached_nodes;

            // Continue until we've logged more layers than we have reached nodes (Hall violator)
            all_reached_nodes.insert(new_reached_nodes.begin(), new_reached_nodes.end());
            count++;
        }

        // In order to actually get the contradiction we need to retrieve the at_least_1_constraints
        // and in order to do that we need a clique of not-equals over the vars
        state.infer_true(JustifyExplicitly{
            [&](Proof & proof) {
                for (const auto & i : all_reached_nodes) {
                    stringstream proofline;
                    if (shifted_pos[i].size() > 1) {
                        auto k = ++shifted_pos[i].begin();
                        auto l = shifted_pos[i].begin();
                        proofline << "p " << prove_not_both(i, (*l).first, (*k).first, distance_at_least, distance, shifted_pos, n, state);
                        vector<ProofLine> neq_lines{};
                        k++;
                        auto k_count = 2;
                        while (k != shifted_pos[i].end()) {
                            proofline << " " << k_count << " * ";
                            l = shifted_pos[i].begin();
                            while (l != k) {
                                proofline << prove_not_both(i, (*l).first, (*k).first, distance_at_least, distance, shifted_pos, n, state) << " + ";
                                l++;
                            }
                            proofline << k_count + 1 << " d ";
                            k++;
                            k_count++;
                        }
                        proof.emit_proof_comment("AM1");
                        am1_q_lines.emplace_back(proof.emit_proof_line(proofline.str(), ProofLevel::Current));
                    }
                    else if (shifted_pos[i].size() == 1) {
                        proof.emit_proof_comment("AM1");
                        am1_q_lines.emplace_back(proof.emit_rup_proof_line(WeightedPseudoBooleanSum{} + 1_i * ! assumption + 1_i * ! ((*shifted_pos[i].begin()).second.flag) >= 0_i, ProofLevel::Current));
                    }
                }
            }});

        // Finally we can derive our contradiction from the AL1 and AM1 lines
        state.infer_true(JustifyExplicitly{
            [&](Proof & proof) {
                stringstream proofline;
                proofline << "p ";
                proofline << al1_q_lines[0] << " ";

                for (auto it = al1_q_lines.begin() + 1; it < al1_q_lines.end(); it++) {
                    proofline << *it << " + ";
                }

                for (auto it = am1_q_lines.begin(); it < am1_q_lines.end(); it++) {
                    proofline << *it << " + ";
                }

                proof.emit_proof_line(proofline.str(), ProofLevel::Current);
            }});
    }

    auto explore(const long & node,
        long & count,
        vector<long> & lowlink,
        vector<long> & visit_number,
        long & start_prev_subtree,
        long & end_prev_subtree,
        long & prev_subroot,
        long & root,
        const bool & prune_skip,
        const vector<IntegerVariableID> & succ,
        const PosVarDataMap & pos_var_data,
        State & state) -> pair<Inference, vector<pair<long, long>>>
    {
        visit_number[node] = count;
        lowlink[node] = count;
        count++;
        Inference result = gcs::innards::Inference::NoChange;
        vector<pair<long, long>> back_edges{};
        state.for_each_value_while(succ[node], [&](Integer w) -> bool {
            if (visit_number[w.raw_value] == -1) {
                auto explore_result = explore(w.raw_value, count, lowlink, visit_number, start_prev_subtree, end_prev_subtree, prev_subroot, root, prune_skip, succ, pos_var_data, state);
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
                else if (prune_skip && visit_number[w.raw_value] < start_prev_subtree) {
                    state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                        proof.emit_proof_comment("Pruning edge (" + to_string(node) + "," + to_string(w.raw_value) + ")" + " that would skip subtree");
                        prove_unreachable(state, succ, prev_subroot, pos_var_data, succ[node] == w);
                    }});

                    increase_inference_to(result, state.infer(succ[node] != w, NoJustificationNeeded{}));
                }
                lowlink[node] = pos_min(lowlink[node], visit_number[w.raw_value]);
            }

            return true;
        });

        if (lowlink[node] == visit_number[node]) {
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                proof.emit_proof_comment("More than one SCC");
                if (node == root) {
                    int unreachable_node = 0;
                    while (visit_number[unreachable_node] != -1) {
                        unreachable_node++;
                    }
                    prove_unreachable(state, succ, unreachable_node, pos_var_data);
                }
                else {
                    prove_unreachable(state, succ, node, pos_var_data);
                }
            }});
            return make_pair(Inference::Contradiction, back_edges);
        }
        else
            return make_pair(result, back_edges);
    }

    auto check_sccs(const vector<IntegerVariableID> & succ, const bool & prune_root, const bool & fix_req, const bool & prune_skip, const PosVarDataMap & pos_var_data, State & state) -> Inference
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
                auto explore_result = explore(v.raw_value, count, lowlink, visit_number, start_subtree, end_subtree, prev_subroot, root, prune_skip, succ, pos_var_data, state);
                increase_inference_to(result, explore_result.first);
                if (result == Inference::Contradiction) {
                    return false;
                }
                auto back_edges = explore_result.second;

                if (back_edges.empty()) {
                    state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                        proof.emit_proof_comment("No back edges:");
                        prove_unreachable(state, succ, prev_subroot, pos_var_data);
                    }});

                    increase_inference_to(result, Inference::Contradiction);
                    return false;
                }
                else if (fix_req && back_edges.size() == 1) {

                    state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                        proof.emit_proof_comment("Fix required back edge (" + to_string(back_edges[0].first) + ", " + to_string(back_edges[0].second) + "):");
                        prove_unreachable(state, succ, back_edges[0].first, pos_var_data, succ[back_edges[0].first] != Integer{back_edges[0].second});
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
                prove_unreachable(state, succ, root, pos_var_data);
            }});

            return Inference::Contradiction;
        }

        if (prune_root && start_subtree > 1) {
            state.for_each_value_while(succ[root], [&](Integer v) -> bool {
                if (visit_number[v.raw_value] < start_subtree) {
                    state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                        proof.emit_proof_comment("Prune impossible edges from root node:");
                        prove_unreachable(state, succ, root, pos_var_data, succ[root] == v);
                    }});

                    increase_inference_to(result, state.infer(succ[root] != v, JustifyUsingRUP{}));
                }

                return true;
            });
        }

        return result;
    }

    auto propagate_circuit_using_scc(const vector<IntegerVariableID> & succ, const bool & prune_root,
        const bool & fix_req, const bool & prune_skip, const PosVarDataMap & pos_var_data, const ConstraintStateHandle & unassigned_handle, State & state)
        -> Inference
    {
        auto result = propagate_non_gac_alldifferent(unassigned_handle, state);
        if (result == Inference::Contradiction) return result;
        increase_inference_to(result, check_sccs(succ, prune_root, fix_req, prune_skip, pos_var_data, state));
        if (result == Inference::Contradiction) return result;
        increase_inference_to(result, prevent_small_cycles(succ, pos_var_data, unassigned_handle, state));
        return result;
    }
}

auto CircuitSCC::clone() const -> unique_ptr<Constraint>
{
    return make_unique<CircuitSCC>(_succ, _gac_all_different);
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

    Triggers triggers;
    triggers.on_change = {_succ.begin(), _succ.end()};
    propagators.install(
        [succ = _succ,
            pos_var_data = pos_var_data,
            unassigned_handle = unassigned_handle](State & state) -> pair<Inference, PropagatorState> {
            auto result = propagate_circuit_using_scc(succ, true, true, true, pos_var_data, unassigned_handle, state);
            return pair{result, PropagatorState::Enable};
        },
        triggers,
        "circuit");
}