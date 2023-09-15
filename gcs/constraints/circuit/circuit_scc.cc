#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/innards/propagators.hh>
#include <iostream>
#include <list>
#include <set>
#include <string>
#include <utility>
#include <vector>

using std::cmp_not_equal;
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
    auto select_root() -> long
    {
        // Might have better root selection in future
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

    auto check_sccs(const vector<IntegerVariableID> & succ, const bool & prune_root, const bool & fix_req,
        const bool & prune_skip, const ProofLine2DMap &, const vector<ProofOnlySimpleIntegerVariableID> &, State & state) -> Inference
    {
        auto result = Inference::NoChange;
        auto root = select_root();
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
                    increase_inference_to(result, state.infer(succ[back_edges[0].first] == Integer{back_edges[0].second}, JustifyUsingAssertion{}));
                }
                start_subtree = end_subtree + 1;
                end_subtree = count - 1;
            }
            return true;
        });

        if (cmp_not_equal(count, succ.size())) {
            // The graph isn't even connected
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
        const ProofLine2DMap & lines_for_setting_pos, const ConstraintStateHandle & unassigned_handle, State & state)
        -> Inference
    {
        auto result = propagate_non_gac_alldifferent(unassigned_handle, state);
        if (result == Inference::Contradiction) return result;
        increase_inference_to(result, check_sccs(succ, prune_root, fix_req, prune_skip, lines_for_setting_pos, pos_vars, state));
        if (result == Inference::Contradiction) return result;
        increase_inference_to(result, prevent_small_cycles(succ, lines_for_setting_pos, unassigned_handle, state));
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
    auto lines_for_setting_pos = get<1>(set_up_results);

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
            pos_vars = pos_vars,
            lines_for_setting_pos = lines_for_setting_pos,
            unassigned_handle = unassigned_handle](State & state) -> pair<Inference, PropagatorState> {
            auto result = propagate_circuit_using_scc(succ, false, false, false, pos_vars, lines_for_setting_pos, unassigned_handle, state);
            return pair{result, PropagatorState::Enable};
        },
        triggers,
        "circuit");
}