#include <gcs/constraints/regular.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

#include <functional>
#include <list>
#include <optional>
#include <set>
#include <sstream>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::move;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::unordered_map;
using std::vector;
using std::visit;
using std::make_pair;

namespace
{
    auto initialise_graph(const vector<IntegerVariableID> & vars, const vector<Integer> & symbols,
        const long & num_states, vector<unordered_map<Integer, long>> & transitions,
        const vector<long> & final_states, vector<vector<ProofFlag>> & state_at_pos_flags, State & state, Propagators & propagators) -> unsigned long
    {
        const auto num_vars = static_cast<long>(vars.size());
        RegularGraph graph = RegularGraph(num_vars, num_states);

        // Forward phase: accumulate
        graph.nodes[0].insert(0);
        for (unsigned long i = 0; i < num_vars; ++i) {
            state.for_each_value(vars[i], [&](Integer val) -> void {
                for (const auto & q : graph.nodes[i]) {
                    if (transitions[q][val] != -1) {
                        graph.states_supporting[i][val].insert(q);
                        graph.nodes[i + 1].insert(transitions[q][val]);
                    }
                }
            });

            // TODO: This is messy - could do with refactoring, but I think it's the inference we need
            if (state.maybe_proof()) {
                for (long next_q = 0; next_q < num_states; ++next_q) {
                    if (graph.nodes[i + 1].contains(next_q)) continue;
                    // Want to eliminate this node i.e. prove !state[i+1][next_q]
                    for (const auto & q : graph.nodes[i]) {
                        // So first eliminate each previous state/variable combo
                        state.for_each_value(vars[i], [&](Integer val) -> void {
                            state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
                                stringstream proof_step;
                                proof_step << "u ";
                                proof_step << proof.trail_variables(state, 1_i);
                                proof_step << " 1 " << proof.proof_variable(vars[i] != val);
                                proof_step << " 1 " << proof.proof_variable(! state_at_pos_flags[i][q]);
                                proof_step << " 1 " << proof.proof_variable(! state_at_pos_flags[i + 1][next_q]);
                                proof_step << " >= 1 ;";
                                proof.emit_proof_line(proof_step.str());
                            }});
                        });

                        // Then eliminate each previous state
                        state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
                            stringstream proof_step;
                            proof_step << "u ";
                            proof_step << proof.trail_variables(state, 1_i);
                            proof_step << " 1 " << proof.proof_variable(! state_at_pos_flags[i][q]);
                            proof_step << " 1 " << proof.proof_variable(! state_at_pos_flags[i+1][next_q]);
                            proof_step << " >= 1 ;";
                            proof.emit_proof_line(proof_step.str());
                        }});
                    }

                    // Finally, can eliminate what we want
                    state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
                        stringstream proof_step;
                        proof_step << "u ";
                        proof_step << proof.trail_variables(state, 1_i);
                        proof_step << " 1 " << proof.proof_variable(! state_at_pos_flags[i+1][next_q]);
                        proof_step << " >= 1 ;";
                        proof.emit_proof_line(proof_step.str());
                    }});
                }
            }
        }
        set<long> possible_final_states;
        for (const auto & f : final_states) {
            if (graph.nodes[num_vars].contains(f))
                possible_final_states.insert(f);
        }

        graph.nodes[num_vars] = possible_final_states;

        // Backward phase: validate
        for (long i = num_vars - 1; i >= 0; --i) {

            unordered_map<long, bool> state_is_support;
            for (const auto & q : graph.nodes[i]) {
                state_is_support[q] = false;
            }

            state.for_each_value(vars[i], [&](Integer val) -> void {
                set<long> states = graph.states_supporting[i][val];
                for (const auto & q : states) {

                    if (graph.nodes[i + 1].contains(transitions[q][val])) {

                        graph.out_edges[i][q][transitions[q][val]].emplace(val);
                        graph.out_deg[i][q]++;
                        graph.in_edges[i + 1][transitions[q][val]][q].emplace(val);
                        graph.in_deg[i][transitions[q][val]]++;
                        state_is_support[q] = true;
                    }
                    else {
                        graph.states_supporting[i][val].erase(q);
                        state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
                            stringstream proof_step;
                            proof_step << "u ";
                            proof_step << proof.trail_variables(state, 1_i);
                            proof.need_proof_variable(vars[i] != val);
                            proof_step << " 1 " << proof.proof_variable(vars[i] != val);
                            proof_step << " 1 " << proof.proof_variable(! state_at_pos_flags[i][q]);
                            proof_step << " >= 1 ;";
                            proof.emit_proof_line(proof_step.str());
                        }});
                    }
                }
            });

            set<long> gn = graph.nodes[i];
            for (const auto & q : gn) {
                if (! state_is_support[q]) {
                    graph.nodes[i].erase(q);
                    state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
                        stringstream proof_step;
                        proof_step << "u ";
                        proof_step << proof.trail_variables(state, 1_i);
                        proof_step << " 1 " << proof.proof_variable(! state_at_pos_flags[i][q]);
                        proof_step << " >= 1 ;";
                        proof.emit_proof_line(proof_step.str());
                    }});
                }
            }
        }
        return state.add_constraint_state(graph);
    }

    auto decrement_outdeg(RegularGraph& graph, const long i, const long k) -> void {
        graph.out_deg[i][k]--;
        if(graph.out_deg[i][k] == 0 && i > 0) {
            for(const auto& edge : graph.in_edges[i][k]) {
                auto l = edge.first;
                graph.in_edges[i-1][l].erase(k);
                for(const auto& val : edge.second)
                    graph.states_supporting[i-1][val].erase(l);
                decrement_outdeg(graph, i-1, l);
            }
            graph.in_edges[i][k] = {};
        }
    }

    auto decrement_indeg(RegularGraph& graph, const long i, const long k) -> void {
        graph.in_deg[i][k]--;
        if(graph.in_deg[i][k] == 0 && i < graph.in_deg.size()-1) {
            for(const auto& edge : graph.out_edges[i][k]) {
                auto l = edge.first;
                graph.in_edges[i+1][l].erase(k);
                for(const auto& val : edge.second)
                    graph.states_supporting[i][val].erase(l);
                decrement_indeg(graph, i+1, l);
            }
            graph.out_edges[i][k] = {};
        }
    }
    auto propagate_regular(const vector<IntegerVariableID> & vars,
        const unsigned long graph_idx,
        vector<unordered_map<Integer, long>> transitions,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        State & state) -> Inference
    {
        const auto num_vars = vars.size();

        auto graph = get<RegularGraph>(state.get_constraint_state(graph_idx));
        bool changed = false;
        bool contradiction = false;

        for (int i = 0; i < graph.states_supporting.size(); i++) {
            for(const auto& val_and_states : graph.states_supporting[i]) {
                auto val = val_and_states.first;
                // Clean up domains
                if (graph.states_supporting[i][val].empty() && !state.in_domain(vars[i], val)) {
                    for(const auto& q : graph.states_supporting[i][val]) {
                        auto next_q = transitions[i][val];
                        if(graph.out_edges[i][q].contains(next_q))
                            graph.out_edges[i][q][next_q].erase(val);

                        if(graph.out_edges[i][q][next_q].empty())
                            graph.out_edges[i][q].erase(next_q);

                        if(graph.in_edges[i+1][next_q].contains(q))
                            graph.out_edges[i+1][next_q][q].erase(val);

                        if(graph.out_edges[i+1][next_q][q].empty())
                            graph.out_edges[i+1][next_q].erase(q);

                        decrement_outdeg(graph, i, q);
                        decrement_indeg(graph, i, next_q);
                    }
                    graph.states_supporting[i][val] = {};
                }
            }
        }


        for (int i = 0; i < graph.states_supporting.size(); i++) {
            state.for_each_value(vars[i], [&](Integer val) -> void {
                // Clean up domains
                if (graph.states_supporting[i][val].empty()) {
                    switch (state.infer_not_equal(vars[i], val, JustifyUsingRUP{})) {
                        case Inference::Contradiction:
                            contradiction = true;
                            break;
                        case Inference::Change:
                            changed = true;
                            break;
                        case Inference::NoChange:
                            break;
                    }
                }
            });
        }

        if (contradiction)
            return Inference::Contradiction;
        else if (changed)
            return Inference::Change;
        return Inference::NoChange;
    }
}

Regular::Regular(vector<IntegerVariableID> v, vector<Integer> s, long n, vector<unordered_map<Integer, long>> t, vector<long> f) :
    _vars(move(v)),
    _symbols(move(s)),
    _num_states(n),
    _transitions(move(t)),
    _final_states(move(f))
{
}

Regular::Regular(vector<IntegerVariableID> v, vector<Integer> s, long n, vector<vector<long>> transitions, vector<long> f) :
        _vars(move(v)),
        _symbols(move(s)),
        _num_states(n),
        _transitions(vector<unordered_map<Integer, long>>(n, unordered_map<Integer, long>{})),
        _final_states(move(f))
{
    for(int i = 0; i < transitions.size(); i++) {
        for(int j = 0; j < transitions[i].size(); j++) {
            _transitions[i][Integer{j}]= transitions[i][j];
        }
    }

}

auto Regular::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Regular>(_vars, _symbols, _num_states, _transitions, _final_states);
}

auto Regular::install(Propagators & propagators, State & initial_state) && -> void
{

    vector<vector<ProofFlag>> state_at_pos_flags;
    if (propagators.want_definitions()) {
        // Make 2D array of flags: state_at_pos_flags[i][q] means the DFA is in state q when it receives the
        // input value from vars[i], with an extra row of flags for the state after the last transition.
        // NB: Might be easier to have a 1D array of ProofOnlyIntegerVariables, but making literals of these is
        // awkward currently. (TODO ?)
        for (unsigned int idx = 0; idx <= _vars.size(); ++idx) {
            WeightedPseudoBooleanTerms exactly_1_true{};
            state_at_pos_flags.emplace_back();
            for (unsigned int q = 0; q < _num_states; ++q) {
                state_at_pos_flags[idx].emplace_back(propagators.create_proof_flag("state" + to_string(idx) + "is" + to_string(q)));
                exactly_1_true.emplace_back(1_i, state_at_pos_flags[idx][q]);
            }
            propagators.define_pseudoboolean_eq(initial_state, move(exactly_1_true), 1_i);
        }

        // State at pos 0 is 0
        propagators.define_pseudoboolean_ge(initial_state, {{1_i, state_at_pos_flags[0][0]}}, 1_i);
        // State at pos n is one of the final states
        WeightedPseudoBooleanTerms pos_n_states;
        for (const auto & f : _final_states) {
            pos_n_states.emplace_back(1_i, state_at_pos_flags[_vars.size()][f]);
        }
        propagators.define_pseudoboolean_ge(initial_state, move(pos_n_states), 1_i);

        for (unsigned int idx = 0; idx < _vars.size(); ++idx) {
            for (unsigned int q = 0; q < _num_states; ++q) {
                for (const auto & val : _symbols) {
                    if (_transitions[q][val] == -1) {
                        // No transition for q, v, so constrain ~(state_i = q /\ X_i = val)
                        propagators.define_pseudoboolean_ge(initial_state, {{1_i, _vars[idx] != val}, {1_i, ! state_at_pos_flags[idx][q]}}, 1_i);
                    }
                    else {
                        auto new_q = _transitions[q][val];
                        propagators.define_pseudoboolean_ge(initial_state, {{1_i, ! state_at_pos_flags[idx][q]}, {1_i, _vars[idx] != val}, {1_i, state_at_pos_flags[idx + 1][new_q]}}, 1_i);
                    }
                }
            }
        }
    }

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    auto graph_idx = initialise_graph(_vars, _symbols, _num_states, _transitions, _final_states, state_at_pos_flags, initial_state, propagators);

    propagators.install([v = move(_vars), g = graph_idx, t = move(_transitions), flags = state_at_pos_flags](State & state) -> pair<Inference, PropagatorState> {
        return pair{propagate_regular(v, g, t, flags, state), PropagatorState::Enable};
    },
        triggers, "regular");
}

auto Regular::describe_for_proof() -> string
{
    return "regular";
}
