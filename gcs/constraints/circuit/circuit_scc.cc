#include <cstdlib>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>
#include <iostream>
#include <list>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using std::cout;
using std::list;
using std::min;
using std::pair;
using std::set;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

namespace
{
    auto select_root(const vector<IntegerVariableID> & succ, State & state) -> long
    {
        // Generate a random integer n between 0 (inclusive) and succ.size() (exclusive)
        long n = rand() % succ.size();
        return n;
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

    auto explore(const long & node, long & count, vector<long> & lowlink, vector<long> & visit_number, long & start_prev_subtree, long & end_prev_subtree, const bool & prune_skip, const vector<IntegerVariableID> & succ, State & state) -> pair<Inference, vector<pair<long, long>>>
    {
        visit_number[node] = count;
        lowlink[node] = count;
        count++;
        Inference result = gcs::innards::Inference::NoChange;
        vector<pair<long, long>> back_edges{};
        state.for_each_value_while(succ[node], [&](Integer w) -> bool {
            if (visit_number[w.raw_value] == -1) {
                auto explore_result = explore(w.raw_value, count, lowlink, visit_number, start_prev_subtree, end_prev_subtree, prune_skip, succ, state);
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
                    increase_inference_to(result, state.infer(succ[node] != w, JustifyUsingRUP{}));
                }
                lowlink[node] = pos_min(lowlink[node], visit_number[w.raw_value]);
            }

            return true;
        });

        if (lowlink[node] == visit_number[node]) {

            return make_pair(Inference::Contradiction, back_edges);
        }
        else
            return make_pair(result, back_edges);
    }

    auto justify_disconnected_component(long root, const vector<IntegerVariableID> & succ, const ConstraintStateHandle & prev_wlog_line_handle, const vector<ProofOnlySimpleIntegerVariableID> & pos_vars, State & state)
    {
        set<long> curr_reachable = {root};
        set<long> new_reachable = {root};
        set<long> curr_reachable_in_n = {root};
        set<long> new_reachable_in_n = {root};
        wlog_choose_vertex_as_position_0(root, succ, prev_wlog_line_handle, pos_vars, state);

        auto steps = 1;
        do {
            curr_reachable = new_reachable;
            new_reachable_in_n = {};
            for (auto val : curr_reachable_in_n) {
                set<long> next_from_val = {};
                state.for_each_value(succ[val], [&](Integer v) -> void {
                    new_reachable_in_n.insert(v.raw_value);
                    new_reachable.insert(v.raw_value);
                    next_from_val.insert(v.raw_value);
                });
                state.infer_true(JustifyExplicitly{
                    [&](Proof & proof, vector<ProofLine> & del) {
                        WeightedPseudoBooleanSum pos_sum{};
                        pos_sum += 1_i * (pos_vars[val] != Integer{steps - 1});
                        for (auto node : next_from_val) {
                            pos_sum += 1_i * (pos_vars[node] == Integer{steps});
                        }
                        proof.emit_proof_comment("pos[" + to_string(steps - 1) + "] = " + to_string(val) + " => ");
                        proof.emit_rup_proof_line_under_trail(state, pos_sum >= 1_i);
                    }});
            }

            state.infer_true(JustifyExplicitly{
                [&](Proof & proof, vector<ProofLine> & del) {
                    WeightedPseudoBooleanSum pos_sum{};
                    for (auto node : new_reachable) {
                        pos_sum += 1_i * (pos_vars[node] == Integer{steps});
                    }
                    proof.emit_proof_comment("Reachable after " + to_string(steps) + " steps:");
                    proof.emit_rup_proof_line_under_trail(state, pos_sum >= 1_i);
                }});
            steps++;
        } while (curr_reachable.size() != new_reachable.size());
    }

    auto check_sccs(const vector<IntegerVariableID> & succ, const bool & prune_root, const bool & fix_req,
        const bool & prune_skip, const ConstraintStateHandle & prev_wlog_line_handle, const vector<ProofOnlySimpleIntegerVariableID> & pos_vars, State & state) -> Inference
    {
        auto result = Inference::NoChange;
        auto root = select_root(succ, state);
        long count = 1;
        long start_subtree = 0;
        long end_subtree = 0;

        vector<long> lowlink = vector<long>(succ.size(), -1);
        vector<long> visit_number = vector<long>(succ.size(), -1);
        lowlink[root] = 0;
        visit_number[root] = 0;

        state.for_each_value_while(succ[root], [&](Integer v) -> bool {
            if (visit_number[v.raw_value] == -1) {
                auto explore_result = explore(v.raw_value, count, lowlink, visit_number, start_subtree, end_subtree, prune_skip, succ, state);
                increase_inference_to(result, explore_result.first);
                if (result == Inference::Contradiction) {
                    return false;
                }
                auto back_edges = explore_result.second;

                if (back_edges.empty()) {
                    state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) {
                        proof.emit_proof_comment("No back edges:");
                    }});
                    increase_inference_to(result, Inference::Contradiction);
                    return false;
                }
                else if (fix_req && back_edges.size() == 1) {
                    state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) {
                        proof.emit_proof_comment("Fix required edge from root node:");
                    }});
                    increase_inference_to(result, state.infer(succ[back_edges[0].first] == Integer{back_edges[0].second}, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) {
                        cout << "Doing something?";
                        proof.emit_proof_comment("hmm");
                        proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * (succ[back_edges[0].first] == Integer{back_edges[0].second}) >= 1_i);
                    }}));
                }
                start_subtree = end_subtree + 1;
                end_subtree = count - 1;
            }
            return true;
        });

        if (count != succ.size()) {
            // The graph isn't even connected
            justify_disconnected_component(0, succ, prev_wlog_line_handle, pos_vars, state);
            return Inference::Contradiction;
        }

        if (prune_root && start_subtree > 1) {
            state.for_each_value_while(succ[root], [&](Integer v) -> bool {
                if (visit_number[v.raw_value] < start_subtree) {
                    state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) {
                        proof.emit_proof_comment("Prune impossible edges from root node:");
                    }});
                    increase_inference_to(result, state.infer(succ[root] != v, JustifyUsingRUP{}));
                }

                return true;
            });
        }

        return result;
    }

    auto propagate_circuit_using_scc(const vector<IntegerVariableID> & succ, const bool & prune_root,
        const bool & fix_req, const bool & prune_skip, const vector<ProofOnlySimpleIntegerVariableID> & pos_vars,
        const ConstraintStateHandle & prev_wlog_line_handle, const ConstraintStateHandle & unassigned_handle, State & state)
        -> Inference
    {
        auto result = propagate_non_gac_alldifferent(unassigned_handle, state);
        if (result == Inference::Contradiction) return result;
        increase_inference_to(result, check_sccs(succ, prune_root, fix_req, prune_skip, prev_wlog_line_handle, pos_vars, state));
        //        if (result == Inference::Contradiction) return result;
        //        increase_inference_to(result, prevent_small_cycles(succ, prev_wlog_line_handle, unassigned_handle, pos_vars, state));
        return result;
    }
}

auto CircuitSCC::clone() const -> unique_ptr<Constraint>
{
    return make_unique<CircuitSCC>(_succ, _gac_all_different);
}

auto CircuitSCC::install(Propagators & propagators, State & initial_state) && -> void
{
    auto set_up_results = CircuitBase::set_up(propagators, initial_state);
    auto pos_vars = get<0>(set_up_results);
    auto prev_wlog_line_handle = get<1>(set_up_results);
    auto unassigned_handle = get<2>(set_up_results);

    Triggers triggers;
    triggers.on_change = {_succ.begin(), _succ.end()};
    propagators.install(
        [succ = _succ,
            pos_vars = pos_vars,
            prev_wlog_line_handle = prev_wlog_line_handle,
            unassigned_handle = unassigned_handle](State & state) -> pair<Inference, PropagatorState> {
            auto result = propagate_circuit_using_scc(succ, false, false, false, pos_vars, prev_wlog_line_handle, unassigned_handle, state);
            return pair{result, PropagatorState::Enable};
        },
        triggers,
        "circuit");
}
