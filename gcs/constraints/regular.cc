#include <gcs/constraints/regular.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

#include <any>
#include <cstdio>
#include <fstream>
#include <functional>
#include <iostream>
#include <list>
#include <optional>
#include <set>
#include <sstream>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::any_cast;
using std::cmp_less;
using std::cmp_not_equal;
using std::cout;
using std::endl;
using std::fstream;
using std::getline;
using std::ifstream;
using std::ios;
using std::make_pair;
using std::move;
using std::ofstream;
using std::optional;
using std::pair;
using std::rename;
using std::set;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;
using std::visit;

namespace
{
    struct RegularGraph
    {
        vector<unordered_map<Integer, set<long>>> states_supporting;
        vector<vector<unordered_map<long, unordered_set<Integer>>>> out_edges;
        vector<vector<long>> out_deg;
        vector<vector<unordered_map<long, unordered_set<Integer>>>> in_edges;
        vector<vector<long>> in_deg;
        vector<set<long>> nodes;
        bool initialised;

        explicit RegularGraph(long num_vars, long num_states) :
            states_supporting(vector<unordered_map<Integer, set<long>>>(num_vars)),
            out_edges(vector<vector<unordered_map<long, unordered_set<Integer>>>>(num_vars, vector<unordered_map<long, unordered_set<Integer>>>(num_states))),
            out_deg(vector<vector<long>>(num_vars, vector<long>(num_states, 0))),
            in_edges(vector<vector<unordered_map<long, unordered_set<Integer>>>>(num_vars + 1, vector<unordered_map<long, unordered_set<Integer>>>(num_states))),
            in_deg(vector<vector<long>>(num_vars + 1, vector<long>(num_states, 0))),
            nodes(vector<set<long>>(num_vars + 1)),
            initialised(false)
        {
        }
    };

    auto print_graph_edges(const RegularGraph & graph, const string & output_file_name)
    {
        // Remove last line of file (...very hacky)
        ifstream in(output_file_name);

        ofstream out("temp.tmp");

        string line;
        getline(in, line);
        for (string tmp; getline(in, tmp); line.swap(tmp)) {
            out << line << '\n';
        }
        out.close();
        rename("temp.tmp", output_file_name.c_str());

        ofstream output_file(output_file_name, ios::app);
        // Debugging and demonstration purposes only
        output_file << "[";
        int l = 0;
        for (const auto & layer : graph.out_edges) {
            output_file << "\t[";
            int k = 0;
            for (const auto & node : layer) {
                output_file << "{";
                int j = 0;
                for (const auto & state_and_vals : node) {
                    if(graph.in_edges[l+1][state_and_vals.first].contains(k)) {
                        output_file << state_and_vals.first << ": [";
                        int i = 0;
                            for (const auto &val: state_and_vals.second) {
                                if(graph.in_edges[l+1][state_and_vals.first].at(k).contains(val)) {
                                    output_file << val.raw_value;
                                    if (cmp_not_equal(i, state_and_vals.second.size() - 1))
                                        output_file << ", ";
                                    i++;
                                }

                            }
                        output_file << "]";
                    if (cmp_not_equal(j, node.size() - 1))
                        output_file << ",";
                    }
                    j++;
                }
                output_file << "}";
                if (cmp_not_equal(k, layer.size() - 1))
                    output_file << ",";
                k++;
            }
            output_file << "]";
            if (cmp_not_equal(l, graph.out_edges.size() - 1)) {
                output_file << ",\n";
            }
            l++;
        }
        output_file << "],\n";
        output_file << "]";
        output_file.close();
    }

    auto log_additional_inference(const vector<Literal> & literals, const vector<ProofFlag> & proof_flags, State & state, string comment = "") -> void
    {
        // Trying to cut down on repeated code
        state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
            if (! comment.empty()) {
                proof.emit_proof_comment(comment);
            }
            stringstream proof_step;
            proof_step << "u ";
            proof_step << proof.trail_variables(state, 1_i);
            for (const auto & lit : literals) {
                proof.need_proof_variable(lit);
                proof_step << " 1 " << proof.proof_variable(lit);
            }

            for (const auto & flag : proof_flags) {
                proof_step << " 1 " << proof.proof_variable(flag);
            }
            proof_step << " >= 1 ;";
            proof.emit_proof_line(proof_step.str());
        }});
    }

    auto initialise_graph(RegularGraph & graph, const vector<IntegerVariableID> & vars,
        const long num_states, vector<unordered_map<Integer, long>> & transitions,
        const vector<long> & final_states, const vector<vector<ProofFlag>> & state_at_pos_flags, State & state)
    {
        auto num_vars = vars.size();
        state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
            proof.emit_proof_comment("Initialising graph");
        }});
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

            if (state.maybe_proof()) {
                for (long next_q = 0; next_q < num_states; ++next_q) {
                    if (graph.nodes[i + 1].contains(next_q)) continue;
                    // Want to eliminate this node i.e. prove !state[i+1][next_q]
                    for (const auto & q : graph.nodes[i]) {
                        // So first eliminate each previous state/variable combo
                        state.for_each_value(vars[i], [&](Integer val) -> void {
                            log_additional_inference({vars[i] != val}, {! state_at_pos_flags[i][q], ! state_at_pos_flags[i + 1][next_q]}, state);
                        });

                        // Then eliminate each previous state
                        log_additional_inference({}, {! state_at_pos_flags[i][q], ! state_at_pos_flags[i + 1][next_q]}, state);
                    }

                    // Finally, can eliminate what we want
                    log_additional_inference({}, {! state_at_pos_flags[i + 1][next_q]}, state);
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
                        graph.in_deg[i + 1][transitions[q][val]]++;
                        state_is_support[q] = true;
                    }
                    else {
                        graph.states_supporting[i][val].erase(q);
                        log_additional_inference({vars[i] != val}, {! state_at_pos_flags[i][q]}, state);
                    }
                }
            });

            set<long> gn = graph.nodes[i];
            for (const auto & q : gn) {
                if (! state_is_support[q]) {
                    graph.nodes[i].erase(q);
                    log_additional_inference({}, {! state_at_pos_flags[i][q]}, state, "back pass");
                }
            }
        }

        graph.initialised = true;
    }

    auto decrement_outdeg(RegularGraph & graph, const long i, const long k, const vector<IntegerVariableID> & vars,
        const vector<vector<ProofFlag>> & state_at_pos_flags, State & state) -> void
    {
        graph.out_deg[i][k]--;
        if (graph.out_deg[i][k] == 0 && i > 0) {
            for (const auto & edge : graph.in_edges[i][k]) {
                auto l = edge.first;
                graph.out_edges[i - 1][l].erase(k);
                for (const auto & val : edge.second) {
                    graph.states_supporting[i - 1][val].erase(l);
                    log_additional_inference({vars[i - 1] != val}, {! state_at_pos_flags[i - 1][l]}, state, "dec outdeg inner");
                    decrement_outdeg(graph, i - 1, l, vars, state_at_pos_flags, state);
                }
            }
            graph.in_edges[i][k] = {};
            log_additional_inference({}, {! state_at_pos_flags[i][k]}, state, "dec outdeg");
        }
    }

    auto decrement_indeg(RegularGraph & graph, const long i, const long k, const vector<IntegerVariableID> & vars, const vector<vector<ProofFlag>> & state_at_pos_flags, State & state) -> void
    {
        graph.in_deg[i][k]--;
        if (graph.in_deg[i][k] == 0 && cmp_less(i, graph.in_deg.size() - 1)) {
            // Again, want to eliminate this node i.e. prove !state[i][k]
            for (const auto & q : graph.nodes[i - 1]) {
                // So first eliminate each previous state/variable combo
                state.for_each_value(vars[i], [&](Integer val) -> void {
                    log_additional_inference({vars[i] != val}, {! state_at_pos_flags[i - 1][q], ! state_at_pos_flags[i][k]}, state);
                });

                // Then eliminate each previous state
                log_additional_inference({}, {! state_at_pos_flags[i - 1][q], ! state_at_pos_flags[i][k]}, state);
            }

            // Finally, can eliminate what we want
            log_additional_inference({}, {! state_at_pos_flags[i][k]}, state);

            for (const auto & edge : graph.out_edges[i][k]) {
                auto l = edge.first;
                graph.in_edges[i + 1][l].erase(k);

                for (const auto & val : edge.second) {
                    graph.states_supporting[i][val].erase(k);
                    decrement_indeg(graph, i + 1, l, vars, state_at_pos_flags, state);
                }
            }

            graph.out_edges[i][k] = {};
        }
    }

    auto propagate_regular(const vector<IntegerVariableID> & vars,
        const long num_states,
        vector<unordered_map<Integer, long>> transitions,
        const vector<long> & final_states,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const ConstraintStateHandle & graph_handle,
        State & state,
        const bool print_graph,
        const string output_file_name) -> Inference
    {
        auto & graph = any_cast<RegularGraph &>(state.get_constraint_state(graph_handle));

        if (! graph.initialised)
            initialise_graph(graph, vars, num_states, transitions, final_states, state_at_pos_flags, state);

        bool changed = false;
        bool contradiction = false;

        for (size_t i = 0; i < graph.states_supporting.size(); i++) {
            for (const auto & val_and_states : graph.states_supporting[i]) {
                auto val = val_and_states.first;

                if (! graph.states_supporting[i][val].empty() && ! state.in_domain(vars[i], val)) {

                    for (const auto & q : graph.states_supporting[i][val]) {
                        auto next_q = transitions[q][val];

                        if (graph.out_edges[i][q].contains(next_q)) {
                            graph.out_edges[i][q][next_q].erase(val);

                            if (graph.out_edges[i][q][next_q].empty())
                                graph.out_edges[i][q].erase(next_q);
                        }

                        if (graph.in_edges[i + 1][next_q].contains(q)) {
                            graph.in_edges[i + 1][next_q][q].erase(val);

                            if (graph.in_edges[i + 1][next_q][q].empty())
                                graph.in_edges[i + 1][next_q].erase(q);
                        }

                        decrement_outdeg(graph, i, q, vars, state_at_pos_flags, state);
                        decrement_indeg(graph, i + 1, next_q, vars, state_at_pos_flags, state);
                    }
                    graph.states_supporting[i][val] = {};
                }
            }
        }

        for (size_t i = 0; i < graph.states_supporting.size(); i++) {
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

        if (print_graph) {
            print_graph_edges(graph, output_file_name);
        }

        if (contradiction)
            return Inference::Contradiction;
        else if (changed)
            return Inference::Change;
        return Inference::NoChange;
    }
}

Regular::Regular(vector<IntegerVariableID> v, vector<Integer> s, long n, vector<unordered_map<Integer, long>> t, vector<long> f, bool p) :
    _vars(move(v)),
    _symbols(move(s)),
    _num_states(n),
    _transitions(move(t)),
    _final_states(move(f)),
    _print_graph(p),
    _GRAPH_OUTPUT_FILE("regular_graph_output.py")
{
}

Regular::Regular(vector<IntegerVariableID> v, vector<Integer> s, long n, vector<vector<long>> transitions, vector<long> f, bool p) :
    _vars(move(v)),
    _symbols(move(s)),
    _num_states(n),
    _transitions(vector<unordered_map<Integer, long>>(n, unordered_map<Integer, long>{})),
    _final_states(move(f)),
    _print_graph(p)
{
    for (size_t i = 0; i < transitions.size(); i++) {
        for (size_t j = 0; j < transitions[i].size(); j++) {
            _transitions[i][Integer(j)] = transitions[i][j];
        }
    }
}

auto Regular::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Regular>(_vars, _symbols, _num_states, _transitions, _final_states, _print_graph);
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
            WeightedPseudoBooleanSum exactly_1_true{};
            state_at_pos_flags.emplace_back();
            for (unsigned int q = 0; q < _num_states; ++q) {
                state_at_pos_flags[idx].emplace_back(propagators.create_proof_flag("state" + to_string(idx) + "is" + to_string(q)));
                exactly_1_true += 1_i * state_at_pos_flags[idx][q];
            }
            propagators.define_pseudoboolean_eq(initial_state, move(exactly_1_true), 1_i);
        }

        // State at pos 0 is 0
        propagators.define_pseudoboolean_ge(initial_state, WeightedPseudoBooleanSum{} + 1_i * state_at_pos_flags[0][0], 1_i);
        // State at pos n is one of the final states
        WeightedPseudoBooleanSum pos_n_states;
        for (const auto & f : _final_states) {
            pos_n_states += 1_i * state_at_pos_flags[_vars.size()][f];
        }
        propagators.define_pseudoboolean_ge(initial_state, move(pos_n_states), 1_i);

        for (unsigned int idx = 0; idx < _vars.size(); ++idx) {
            for (unsigned int q = 0; q < _num_states; ++q) {
                for (const auto & val : _symbols) {
                    if (_transitions[q][val] == -1) {
                        // No transition for q, v, so constrain ~(state_i = q /\ X_i = val)
                        propagators.define_pseudoboolean_ge(initial_state, WeightedPseudoBooleanSum{} + 1_i * (_vars[idx] != val) + (1_i * state_at_pos_flags[idx][q]), 1_i);
                    }
                    else {
                        auto new_q = _transitions[q][val];
                        propagators.define_pseudoboolean_ge(initial_state, WeightedPseudoBooleanSum{} + 1_i * ! state_at_pos_flags[idx][q] + 1_i * (_vars[idx] != val) + 1_i * state_at_pos_flags[idx + 1][new_q], 1_i);
                    }
                }
            }
        }
    }

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    RegularGraph graph = RegularGraph(_vars.size(), _num_states);
    if (_print_graph) {
        ofstream output_file;
        output_file.open(_GRAPH_OUTPUT_FILE);
        output_file << "graphs = [\n";
        output_file << "]";
        output_file.close();
    }

    auto graph_idx = initial_state.add_constraint_state(graph);
    propagators.install([v = move(_vars), n = _num_states, t = move(_transitions), f = move(_final_states), g = graph_idx, flags = state_at_pos_flags, p = _print_graph, gof = _GRAPH_OUTPUT_FILE](State & state) -> pair<Inference, PropagatorState> {
        return pair{propagate_regular(v, n, t, f, flags, g, state, p, gof), PropagatorState::Enable};
    },
        triggers, "regular");
}

auto Regular::describe_for_proof() -> string
{
    return "regular";
}
