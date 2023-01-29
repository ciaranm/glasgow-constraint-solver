#include <gcs/constraints/regular.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

#include <functional>
#include <list>
#include <optional>
#include <set>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <variant>

// DEBUG ONLY -- REMOVE
#include <iostream>
using std::cout;
using std::endl;
// --------------------

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;
using std::set;
using std::string;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::unordered_map;
using std::vector;
using std::visit;
using std::stringstream;

namespace
{
    auto propagate_regular(const vector<IntegerVariableID> & vars,
        const vector<Integer> & symbols,
        const long num_states,
        const vector<vector<long>> & transitions,
        const vector<long> & final_states,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        State & state) -> Inference
    {
        const auto num_vars = vars.size();
        const auto num_symbols = symbols.size();

        // Might be a better way to initialise these ?
        // -- or better data structures.
        // TODO: Also, obvious would be better to create these once and then incrementally update, as in the paper
        // rather than rebuilding the whole thing every time.
        vector<unordered_map<Integer, set<long>>> states_supporting(num_vars);

        vector<vector<vector<long>>> out_edges(num_vars, vector<vector<long>>(num_states));
        vector<vector<long>> out_deg(num_vars, vector<long>(num_states, 0));
        vector<vector<vector<long>>> in_edges(num_vars + 1, vector<vector<long>>(num_states));
        vector<vector<long>> in_deg(num_vars + 1, vector<long>(num_states, 0));
        vector<set<long>> graph_nodes(num_vars + 1);

        // Forward phase: accumulate
        graph_nodes[0].insert(0);
        for (unsigned long i = 0; i < num_vars; ++i) {
            state.for_each_value(vars[i], [&](Integer val) -> void {
                for (const auto & q : graph_nodes[i]) {
                    if (transitions[q][val.raw_value] != -1) {
                        states_supporting[i][val].insert(q);
                        graph_nodes[i + 1].insert(transitions[q][val.raw_value]);
                    }
                }
            });

            if(state.maybe_proof()) {
                for(const auto& val : symbols) {
                    for (unsigned long q = 0; q < num_states; q++) {
                        if (transitions[q][val.raw_value] == -1) continue;
                        cout << "var[" << i << "] = " << val.raw_value << endl;
                        for(const auto & my_q : states_supporting[i][val]) {
                            cout << my_q << ",";
                        }
                        cout << endl;
                        if (states_supporting[i][val].empty()) {
                            state.infer(TrueLiteral{}, JustifyExplicitly{[&](Proof & proof, vector<ProofLine>&) -> void {
                                stringstream proof_step;
                                proof_step << "u ";
                                state.for_each_guess([&](const Literal & lit) {
                                    if (! is_literally_true(lit))
                                        proof_step << " 1 " << proof.proof_variable(! lit);
                                });
                                proof_step << " 1 " << proof.proof_variable(!state_at_pos_flags[i+1][transitions[q][val.raw_value]]);
                                proof_step << " >= 1 ;\n";
                                proof.emit_proof_line(proof_step.str());
                            }});
                        }
                    }
                }
            }
        }
        set<long> possible_final_states;
        for (const auto & f : final_states) {
            if (graph_nodes[num_vars].contains(f))
                possible_final_states.insert(f);
        }

        graph_nodes[num_vars] = possible_final_states;

        // Backward phase: validate
        for (long i = num_vars - 1; i >= 0; --i) {

            unordered_map<long, bool> state_is_support;
            for (const auto & q : graph_nodes[i]) {
                state_is_support[q] = false;
            }

            state.for_each_value(vars[i], [&](Integer val) -> void {
                set<long> states = states_supporting[i][val];
                for (const auto & q : states) {

                    if (graph_nodes[i + 1].contains(transitions[q][val.raw_value])) {

                        out_edges[i][q].emplace_back(transitions[q][val.raw_value]);
                        out_deg[i][q]++;
                        in_edges[i + 1][transitions[q][val.raw_value]].emplace_back(q);
                        in_deg[i][transitions[q][val.raw_value]]++;
                        state_is_support[q] = true;
                    }
                    else {

                        states_supporting[i][val].erase(q);
                        state.infer(TrueLiteral{}, JustifyExplicitly{[&](Proof & proof, vector<ProofLine>&) -> void {
                            stringstream proof_step;
                            proof_step << "u ";
                            state.for_each_guess([&](const Literal & lit) {
                                if (! is_literally_true(lit))
                                    proof_step << " 1 " << proof.proof_variable(! lit);
                            });
                            proof.need_proof_variable(vars[i] != val);
                            proof_step << " 1 " << proof.proof_variable(vars[i] != val);
                            proof_step << " 1 " << proof.proof_variable(!state_at_pos_flags[i][q]);
                            proof_step << " >= 1 ;\n";
                            proof.emit_proof_line(proof_step.str());
                        }});
                    }
                }
            });

            set<long> gn = graph_nodes[i];
            for (const auto & q : gn) {
                if (! state_is_support[q]) {
                    graph_nodes[i].erase(q);
                    state.infer(TrueLiteral{}, JustifyExplicitly{[&](Proof & proof, vector<ProofLine>&) -> void {
                        stringstream proof_step;
                        proof_step << "u ";
                        state.for_each_guess([&](const Literal & lit) {
                            if (! is_literally_true(lit))
                                proof_step << " 1 " << proof.proof_variable(! lit);
                        });
                        proof_step << " 1 " << proof.proof_variable(!state_at_pos_flags[i][q]);
                        proof_step << " >= 1 ;\n";
                        proof.emit_proof_line(proof_step.str());
                    }});
                }
            }
        }
        bool changed = false;
        bool contradiction = false;

        // Clean up domains
        for (unsigned long i = 0; i < num_vars; ++i) {
            state.for_each_value(vars[i], [&](Integer val) -> void {
                if (states_supporting[i][val].empty()) {
                    switch (state.infer_not_equal(vars[i], val, JustifyUsingRUP{})) {
                    case Inference::Contradiction:
                        contradiction = true;
                    case Inference::Change:
                        changed = true;
                        break;
                    case Inference::NoChange:
                        break;
                    }
                }
            });
        }

        if (contradiction) {
            return Inference::Contradiction;
        }
        else if (changed) {
            return Inference::Change;
        }
        return Inference::NoChange;
    }

    auto convert_re_to_dfa(string regex) -> tuple<vector<Integer>, long, vector<vector<long>>, vector<long>>
    {
        // TODO... maybe
        return tuple<vector<Integer>, long, vector<vector<long>>, vector<long>>{};
    }
}
Regular::Regular(vector<IntegerVariableID> v, vector<Integer> s, long n, vector<vector<long>> t, vector<long> f) :
    _vars(move(v)),
    _symbols(move(s)),
    _num_states(n),
    _transitions(t),
    _final_states(f)
{
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
            pos_n_states.emplace_back(1_i, state_at_pos_flags[_num_states][f]);
        }
        propagators.define_pseudoboolean_ge(initial_state, move(pos_n_states), 1_i);

        for (unsigned int idx = 0; idx < _vars.size(); ++idx) {
            for (unsigned int q = 0; q < _num_states; ++q) {
                for (const auto & val : _symbols) {
                    if (_transitions[q][val.raw_value] == -1) {
                        // No transition for q, v, so constrain ~(state_i = q /\ X_i = val)
                        propagators.define_pseudoboolean_ge(initial_state, {{1_i, _vars[idx] != val}, {1_i, ! state_at_pos_flags[idx][q]}}, 1_i);
                    }
                    else {
                        auto new_q = _transitions[q][val.raw_value];
                        propagators.define_pseudoboolean_ge(initial_state, {{1_i, ! state_at_pos_flags[idx][q]}, {1_i, _vars[idx] != val}, {1_i, state_at_pos_flags[idx + 1][new_q]}}, 1_i);
                    }
                }
            }
        }
    }
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    propagators.install([v = _vars,
                            s = _symbols,
                            n = _num_states,
                            t = _transitions,
                            f = _final_states,
                            flags = state_at_pos_flags](State & state) -> pair<Inference, PropagatorState> {
        return pair{propagate_regular(v, s, n, t, f, flags, state), PropagatorState::Enable};
    },
        triggers, "regular");
}

auto Regular::describe_for_proof() -> string
{
    return "regular";
}
