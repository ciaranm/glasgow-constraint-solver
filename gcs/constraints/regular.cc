#include <gcs/constraints/regular.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <any>
#include <cstdio>
#include <functional>
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
using std::getline;
using std::ios;
using std::move;
using std::optional;
using std::pair;
using std::rename;
using std::set;
using std::string;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

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
        bool initialised = false;

        explicit RegularGraph(long num_vars, long num_states) :
            states_supporting(vector<unordered_map<Integer, set<long>>>(num_vars)),
            out_edges(vector<vector<unordered_map<long, unordered_set<Integer>>>>(num_vars, vector<unordered_map<long, unordered_set<Integer>>>(num_states))),
            out_deg(vector<vector<long>>(num_vars, vector<long>(num_states, 0))),
            in_edges(vector<vector<unordered_map<long, unordered_set<Integer>>>>(num_vars + 1, vector<unordered_map<long, unordered_set<Integer>>>(num_states))),
            in_deg(vector<vector<long>>(num_vars + 1, vector<long>(num_states, 0))),
            nodes(vector<set<long>>(num_vars + 1))
        {
        }
    };

    auto log_additional_inference(ProofLogger * const logger, const vector<Literal> & literals, const vector<ProofFlag> & proof_flags,
        const State & state, const Reason & reason, string comment = "") -> void
    {
        if (logger) {
            // Trying to cut down on repeated code
            if (! comment.empty())
                logger->emit_proof_comment(comment);

            WeightedPseudoBooleanSum terms;
            for (const auto & lit : literals)
                terms += 1_i * lit;
            for (const auto & flag : proof_flags)
                terms += 1_i * flag;
            logger->emit_rup_proof_line_under_reason(state, reason, terms >= 1_i, ProofLevel::Current);
        }
    }

    auto initialise_graph(RegularGraph & graph, const vector<IntegerVariableID> & vars,
        const long num_states, vector<unordered_map<Integer, long>> & transitions,
        const vector<long> & final_states, const vector<vector<ProofFlag>> & state_at_pos_flags,
        const State & state, const Reason & reason, ProofLogger * const logger)
    {
        auto num_vars = vars.size();

        if (logger)
            logger->emit_proof_comment("Initialising graph");

        // Forward phase: accumulate
        graph.nodes[0].insert(0);
        for (unsigned long i = 0; i < num_vars; ++i) {
            for (auto val : state.each_value_immutable(vars[i])) {
                for (const auto & q : graph.nodes[i]) {
                    if (transitions[q][val] != -1) {
                        graph.states_supporting[i][val].insert(q);
                        graph.nodes[i + 1].insert(transitions[q][val]);
                    }
                }
            }

            if (logger) {
                for (long next_q = 0; next_q < num_states; ++next_q) {
                    if (graph.nodes[i + 1].contains(next_q)) continue;
                    // Want to eliminate this node i.e. prove !state[i+1][next_q]
                    for (const auto & q : graph.nodes[i]) {
                        // So first eliminate each previous state/variable combo
                        for (auto val : state.each_value_mutable(vars[i]))
                            log_additional_inference(logger, {vars[i] != val},
                                {! state_at_pos_flags[i][q], ! state_at_pos_flags[i + 1][next_q]}, state, reason);

                        // Then eliminate each previous state
                        log_additional_inference(logger, {}, {! state_at_pos_flags[i][q], ! state_at_pos_flags[i + 1][next_q]},
                            state, reason);
                    }

                    // Finally, can eliminate what we want
                    log_additional_inference(logger, {}, {! state_at_pos_flags[i + 1][next_q]}, state, reason);
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

            for (auto val : state.each_value_mutable(vars[i])) {
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
                        if (logger)
                            log_additional_inference(logger, {vars[i] != val}, {! state_at_pos_flags[i][q]}, state, reason);
                    }
                }
            }

            set<long> gn = graph.nodes[i];
            for (const auto & q : gn) {
                if (! state_is_support[q]) {
                    graph.nodes[i].erase(q);
                    if (logger)
                        log_additional_inference(logger, {}, {! state_at_pos_flags[i][q]}, state, reason, "back pass");
                }
            }
        }

        graph.initialised = true;
    }

    auto decrement_outdeg(RegularGraph & graph, const long i, const long k, const vector<IntegerVariableID> & vars,
        const vector<vector<ProofFlag>> & state_at_pos_flags, const State & state, const Reason & reason, ProofLogger * const logger) -> void
    {
        graph.out_deg[i][k]--;
        if (graph.out_deg[i][k] == 0 && i > 0) {
            for (const auto & edge : graph.in_edges[i][k]) {
                auto l = edge.first;
                graph.out_edges[i - 1][l].erase(k);
                for (const auto & val : edge.second) {
                    graph.states_supporting[i - 1][val].erase(l);
                    if (logger)
                        log_additional_inference(logger, {vars[i - 1] != val}, {! state_at_pos_flags[i - 1][l]}, state, reason,
                            "dec outdeg inner");
                    decrement_outdeg(graph, i - 1, l, vars, state_at_pos_flags, state, reason, logger);
                }
            }
            graph.in_edges[i][k] = {};
            if (logger)
                log_additional_inference(logger, {}, {! state_at_pos_flags[i][k]}, state, reason, "dec outdeg");
        }
    }

    auto decrement_indeg(RegularGraph & graph, const long i, const long k,
        const vector<IntegerVariableID> & vars, const vector<vector<ProofFlag>> & state_at_pos_flags,
        const State & state, const Reason & reason, ProofLogger * const logger) -> void
    {
        graph.in_deg[i][k]--;
        if (graph.in_deg[i][k] == 0 && cmp_less(i, graph.in_deg.size() - 1)) {
            if (logger) {
                // Again, want to eliminate this node i.e. prove !state[i][k]
                for (const auto & q : graph.nodes[i - 1]) {
                    // So first eliminate each previous state/variable combo
                    for (auto val : state.each_value_mutable(vars[i])) {
                        log_additional_inference(logger, {vars[i] != val}, {! state_at_pos_flags[i - 1][q], ! state_at_pos_flags[i][k]},
                            state, reason);
                    }

                    // Then eliminate each previous state
                    log_additional_inference(logger, {}, {! state_at_pos_flags[i - 1][q], ! state_at_pos_flags[i][k]}, state, reason);
                }

                // Finally, can eliminate what we want
                log_additional_inference(logger, {}, {! state_at_pos_flags[i][k]}, state, reason);
            }
            for (const auto & edge : graph.out_edges[i][k]) {
                auto l = edge.first;
                graph.in_edges[i + 1][l].erase(k);

                for (const auto & val : edge.second) {
                    graph.states_supporting[i][val].erase(k);
                    decrement_indeg(graph, i + 1, l, vars, state_at_pos_flags, state, reason, logger);
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
        const State & state,
        InferenceTracker & inference,
        ProofLogger * const logger) -> void
    {
        auto & graph = any_cast<RegularGraph &>(state.get_constraint_state(graph_handle));
        auto reason = generic_reason(state, vars);

        if (! graph.initialised)
            initialise_graph(graph, vars, num_states, transitions, final_states, state_at_pos_flags, state, reason, logger);

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

                        decrement_outdeg(graph, i, q, vars, state_at_pos_flags, state, reason, logger);
                        decrement_indeg(graph, i + 1, next_q, vars, state_at_pos_flags, state, reason, logger);
                    }
                    graph.states_supporting[i][val] = {};
                }
            }
        }

        for (size_t i = 0; i < graph.states_supporting.size(); i++) {
            for (auto val : state.each_value_mutable(vars[i])) {
                // Clean up domains
                if (graph.states_supporting[i][val].empty())
                    inference.infer_not_equal(logger, vars[i], val, JustifyUsingRUP{}, reason);
            }
        }
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
    for (size_t i = 0; i < transitions.size(); i++) {
        for (size_t j = 0; j < transitions[i].size(); j++) {
            _transitions[i][Integer(j)] = transitions[i][j];
        }
    }
}

auto Regular::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Regular>(_vars, _symbols, _num_states, _transitions, _final_states);
}

auto Regular::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    vector<vector<ProofFlag>> state_at_pos_flags;
    if (optional_model) {
        // Make 2D array of flags: state_at_pos_flags[i][q] means the DFA is in state q when it receives the
        // input value from vars[i], with an extra row of flags for the state after the last transition.
        // NB: Might be easier to have a 1D array of ProofOnlyIntegerVariables, but making literals of these is
        // awkward currently. (TODO ?)
        for (unsigned int idx = 0; idx <= _vars.size(); ++idx) {
            WeightedPseudoBooleanSum exactly_1_true{};
            state_at_pos_flags.emplace_back();
            for (unsigned int q = 0; q < _num_states; ++q) {
                state_at_pos_flags[idx].emplace_back(optional_model->create_proof_flag("state" + to_string(idx) + "is" + to_string(q)));
                exactly_1_true += 1_i * state_at_pos_flags[idx][q];
            }
            optional_model->add_constraint(move(exactly_1_true) == 1_i);
        }

        // State at pos 0 is 0
        optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * state_at_pos_flags[0][0] >= 1_i);
        // State at pos n is one of the final states
        WeightedPseudoBooleanSum pos_n_states;
        for (const auto & f : _final_states) {
            pos_n_states += 1_i * state_at_pos_flags[_vars.size()][f];
        }
        optional_model->add_constraint(move(pos_n_states) >= 1_i);

        for (unsigned int idx = 0; idx < _vars.size(); ++idx) {
            for (unsigned int q = 0; q < _num_states; ++q) {
                for (const auto & val : _symbols) {
                    if (_transitions[q][val] == -1) {
                        // No transition for q, v, so constrain ~(state_i = q /\ X_i = val)
                        optional_model->add_constraint(
                            WeightedPseudoBooleanSum{} + 1_i * (_vars[idx] != val) + (1_i * ! state_at_pos_flags[idx][q]) >= 1_i);
                    }
                    else {
                        auto new_q = _transitions[q][val];
                        optional_model->add_constraint(
                            WeightedPseudoBooleanSum{} + 1_i * ! state_at_pos_flags[idx][q] + 1_i * (_vars[idx] != val) + 1_i * state_at_pos_flags[idx + 1][new_q] >= 1_i);
                    }
                }
            }
        }
    }

    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    RegularGraph graph = RegularGraph(_vars.size(), _num_states);
    auto graph_idx = initial_state.add_constraint_state(graph);
    propagators.install([v = move(_vars), n = _num_states, t = move(_transitions), f = move(_final_states), g = graph_idx, flags = state_at_pos_flags](
                const State & state, InferenceTracker & inference, ProofLogger * const logger) -> PropagatorState {
        propagate_regular(v, n, t, f, flags, g, state, inference, logger);
        return PropagatorState::Enable;
    },
        triggers, "regular");
}

auto Regular::describe_for_proof() -> string
{
    return "regular";
}
