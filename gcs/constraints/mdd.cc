#include <gcs/constraints/mdd.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <any>
#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::any_cast;
using std::cmp_less;
using std::make_unique;
using std::move;
using std::set;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

namespace
{
    auto find_transition(const unordered_map<Integer, long> & node_transitions, Integer val) -> long
    {
        auto it = node_transitions.find(val);
        if (it == node_transitions.end())
            return -1L;
        return it->second;
    }

    struct MDDGraph
    {
        // nodes_supporting[i][val] = nodes in layer i that have an outgoing transition on `val`
        // and currently sit on a root-to-accepting path.
        vector<unordered_map<Integer, set<long>>> nodes_supporting;
        // out_edges[i][q] maps target node q' in layer i+1 to the set of values labelling
        // edges q -> q'.
        vector<vector<unordered_map<long, unordered_set<Integer>>>> out_edges;
        vector<vector<long>> out_deg;
        vector<vector<unordered_map<long, unordered_set<Integer>>>> in_edges;
        vector<vector<long>> in_deg;
        // nodes[i] = active nodes in layer i.
        vector<set<long>> nodes;
        bool initialised = false;

        explicit MDDGraph(long num_vars, const vector<long> & nodes_per_layer) :
            nodes_supporting(num_vars),
            out_edges(num_vars),
            out_deg(num_vars),
            in_edges(num_vars + 1),
            in_deg(num_vars + 1),
            nodes(num_vars + 1)
        {
            for (long i = 0; i < num_vars; ++i) {
                out_edges[i].assign(nodes_per_layer[i], {});
                out_deg[i].assign(nodes_per_layer[i], 0L);
            }
            for (long i = 0; i <= num_vars; ++i) {
                in_edges[i].assign(nodes_per_layer[i], {});
                in_deg[i].assign(nodes_per_layer[i], 0L);
            }
        }
    };

    auto log_additional_inference(ProofLogger * const logger, const vector<Literal> & literals,
        const vector<ProofFlag> & proof_flags, const State &, const ReasonFunction & reason,
        string comment = "") -> void
    {
        if (logger) {
            if (! comment.empty())
                logger->emit_proof_comment(comment);

            WPBSum terms;
            for (const auto & lit : literals)
                terms += 1_i * lit;
            for (const auto & flag : proof_flags)
                terms += 1_i * flag;
            logger->emit_rup_proof_line_under_reason(reason, terms >= 1_i, ProofLevel::Current);
        }
    }

    auto initialise_graph(MDDGraph & graph, const vector<IntegerVariableID> & vars,
        const vector<long> & nodes_per_layer,
        const vector<vector<unordered_map<Integer, long>>> & layer_transitions,
        const vector<long> & accepting_terminals,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const State & state, const ReasonFunction & reason, ProofLogger * const logger)
    {
        auto num_vars = vars.size();

        if (logger)
            logger->emit_proof_comment("Initialising MDD graph");

        // Forward phase: nodes reachable from the root with the current domains.
        graph.nodes[0].insert(0);
        for (size_t i = 0; i < num_vars; ++i) {
            for (auto val : state.each_value_immutable(vars[i])) {
                for (const auto & q : graph.nodes[i]) {
                    auto next_q = find_transition(layer_transitions[i][q], val);
                    if (next_q != -1) {
                        graph.nodes_supporting[i][val].insert(q);
                        graph.nodes[i + 1].insert(next_q);
                    }
                }
            }

            if (logger) {
                for (long next_q = 0; next_q < nodes_per_layer[i + 1]; ++next_q) {
                    if (graph.nodes[i + 1].contains(next_q)) continue;
                    // Want to eliminate this node, i.e. prove !state[i+1][next_q].
                    for (const auto & q : graph.nodes[i]) {
                        // First eliminate each previous-state / variable-value combo.
                        for (auto val : state.each_value_mutable(vars[i]))
                            log_additional_inference(logger, {vars[i] != val},
                                {! state_at_pos_flags[i][q], ! state_at_pos_flags[i + 1][next_q]}, state, reason);

                        // Then eliminate each previous state.
                        log_additional_inference(logger, {}, {! state_at_pos_flags[i][q], ! state_at_pos_flags[i + 1][next_q]},
                            state, reason);
                    }

                    // Finally, the conclusion.
                    log_additional_inference(logger, {}, {! state_at_pos_flags[i + 1][next_q]}, state, reason);
                }
            }
        }

        // Restrict the final layer to accepting terminals that are also reachable.
        set<long> reachable_accepting;
        for (auto f : accepting_terminals)
            if (graph.nodes[num_vars].contains(f))
                reachable_accepting.insert(f);

        if (logger) {
            // Non-accepting terminals that the forward pass marked reachable must now be
            // eliminated; their falsity follows by RUP from the "at least one accepting"
            // and "exactly one per layer" OPB constraints.
            for (const auto & q : graph.nodes[num_vars])
                if (! reachable_accepting.contains(q))
                    log_additional_inference(logger, {}, {! state_at_pos_flags[num_vars][q]},
                        state, reason, "non-accepting terminal");
        }
        graph.nodes[num_vars] = reachable_accepting;

        // Backward phase: drop nodes with no path forward to an accepting terminal.
        for (long i = num_vars - 1; i >= 0; --i) {
            vector<char> node_is_support(nodes_per_layer[i], 0);

            for (auto val : state.each_value_mutable(vars[i])) {
                set<long> nodes_for_val = graph.nodes_supporting[i][val];
                for (const auto & q : nodes_for_val) {
                    auto next_q = find_transition(layer_transitions[i][q], val);
                    if (next_q != -1 && graph.nodes[i + 1].contains(next_q)) {
                        graph.out_edges[i][q][next_q].emplace(val);
                        graph.out_deg[i][q]++;
                        graph.in_edges[i + 1][next_q][q].emplace(val);
                        graph.in_deg[i + 1][next_q]++;
                        node_is_support[q] = 1;
                    }
                    else {
                        graph.nodes_supporting[i][val].erase(q);
                        if (logger)
                            log_additional_inference(logger, {vars[i] != val}, {! state_at_pos_flags[i][q]}, state, reason);
                    }
                }
            }

            set<long> gn = graph.nodes[i];
            for (const auto & q : gn) {
                if (! node_is_support[q]) {
                    graph.nodes[i].erase(q);
                    if (logger)
                        log_additional_inference(logger, {}, {! state_at_pos_flags[i][q]}, state, reason, "back pass");
                }
            }
        }

        graph.initialised = true;
    }

    auto decrement_outdeg(MDDGraph & graph, const long i, const long k, const vector<IntegerVariableID> & vars,
        const vector<vector<ProofFlag>> & state_at_pos_flags, const State & state, const ReasonFunction & reason,
        ProofLogger * const logger) -> void
    {
        graph.out_deg[i][k]--;
        if (graph.out_deg[i][k] == 0 && i > 0) {
            for (const auto & edge : graph.in_edges[i][k]) {
                auto l = edge.first;
                graph.out_edges[i - 1][l].erase(k);
                for (const auto & val : edge.second) {
                    graph.nodes_supporting[i - 1][val].erase(l);
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

    auto decrement_indeg(MDDGraph & graph, const long i, const long k, const vector<IntegerVariableID> & vars,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const State & state, const ReasonFunction & reason, ProofLogger * const logger) -> void
    {
        graph.in_deg[i][k]--;
        if (graph.in_deg[i][k] == 0 && cmp_less(i, graph.in_deg.size() - 1)) {
            if (logger) {
                // Eliminate node k in layer i, i.e. prove !state[i][k].
                for (const auto & q : graph.nodes[i - 1]) {
                    for (auto val : state.each_value_mutable(vars[i])) {
                        log_additional_inference(logger, {vars[i] != val},
                            {! state_at_pos_flags[i - 1][q], ! state_at_pos_flags[i][k]}, state, reason);
                    }
                    log_additional_inference(logger, {}, {! state_at_pos_flags[i - 1][q], ! state_at_pos_flags[i][k]},
                        state, reason);
                }
                log_additional_inference(logger, {}, {! state_at_pos_flags[i][k]}, state, reason);
            }
            for (const auto & edge : graph.out_edges[i][k]) {
                auto l = edge.first;
                graph.in_edges[i + 1][l].erase(k);
                for (const auto & val : edge.second) {
                    graph.nodes_supporting[i][val].erase(k);
                    decrement_indeg(graph, i + 1, l, vars, state_at_pos_flags, state, reason, logger);
                }
            }
            graph.out_edges[i][k] = {};
        }
    }

    auto propagate_mdd(const vector<IntegerVariableID> & vars,
        const vector<long> & nodes_per_layer,
        const vector<vector<unordered_map<Integer, long>>> & layer_transitions,
        const vector<long> & accepting_terminals,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const ConstraintStateHandle & graph_handle,
        const State & state, auto & inference, ProofLogger * const logger) -> void
    {
        auto & graph = any_cast<MDDGraph &>(state.get_constraint_state(graph_handle));
        auto reason = generic_reason(state, vars);

        if (! graph.initialised)
            initialise_graph(graph, vars, nodes_per_layer, layer_transitions, accepting_terminals,
                state_at_pos_flags, state, reason, logger);

        for (size_t i = 0; i < graph.nodes_supporting.size(); ++i) {
            for (const auto & val_and_nodes : graph.nodes_supporting[i]) {
                auto val = val_and_nodes.first;

                if (! graph.nodes_supporting[i][val].empty() && ! state.in_domain(vars[i], val)) {
                    for (const auto & q : graph.nodes_supporting[i][val]) {
                        auto next_q = find_transition(layer_transitions[i][q], val);

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
                    graph.nodes_supporting[i][val] = {};
                }
            }
        }

        for (size_t i = 0; i < graph.nodes_supporting.size(); ++i) {
            for (auto val : state.each_value_mutable(vars[i])) {
                if (graph.nodes_supporting[i][val].empty())
                    inference.infer_not_equal(logger, vars[i], val, JustifyUsingRUP{}, reason);
            }
        }
    }
}

MDD::MDD(vector<IntegerVariableID> v,
    vector<vector<unordered_map<Integer, long>>> t,
    vector<long> npl,
    vector<long> ats) :
    _vars(move(v)),
    _layer_transitions(move(t)),
    _nodes_per_layer(move(npl)),
    _accepting_terminals(move(ats))
{
    if (_nodes_per_layer.size() != _vars.size() + 1)
        throw InvalidProblemDefinitionException{"MDD: nodes_per_layer.size() must equal vars.size() + 1"};
    if (_layer_transitions.size() != _vars.size())
        throw InvalidProblemDefinitionException{"MDD: layer_transitions.size() must equal vars.size()"};
    if (_nodes_per_layer.empty() || _nodes_per_layer.front() != 1)
        throw InvalidProblemDefinitionException{"MDD: layer 0 must contain exactly one (root) node"};
    for (size_t i = 0; i < _vars.size(); ++i)
        if (cmp_less(_layer_transitions[i].size(), _nodes_per_layer[i]))
            throw InvalidProblemDefinitionException{format("MDD: layer_transitions[{}] must have one entry per node in layer {}", i, i)};
}

auto MDD::clone() const -> unique_ptr<Constraint>
{
    return make_unique<MDD>(_vars, _layer_transitions, _nodes_per_layer, _accepting_terminals);
}

auto MDD::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto MDD::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _graph_idx = initial_state.add_constraint_state(MDDGraph(static_cast<long>(_vars.size()), _nodes_per_layer));

    // Per-layer OPB alphabet: union of transition-keys for that layer and each variable's
    // initial domain. Values in the domain but with no transition need explicit "no-transition"
    // constraints so the RUP-justified propagator pruning verifies.
    _opb_alphabet.assign(_vars.size(), {});
    for (size_t i = 0; i < _vars.size(); ++i) {
        for (const auto & node_map : _layer_transitions[i])
            for (const auto & [val, _] : node_map)
                _opb_alphabet[i].insert(val);
        for (const auto & val : initial_state.each_value_immutable(_vars[i]))
            _opb_alphabet[i].insert(val);
    }

    return true;
}

auto MDD::define_proof_model(ProofModel & model) -> void
{
    // state_at_pos_flags[i][q] means "the MDD path passes through node q in layer i".
    for (size_t idx = 0; idx <= _vars.size(); ++idx) {
        WPBSum exactly_1_true{};
        _state_at_pos_flags.emplace_back();
        for (long q = 0; q < _nodes_per_layer[idx]; ++q) {
            _state_at_pos_flags[idx].emplace_back(model.create_proof_flag(format("mddnode{}is{}", idx, q)));
            exactly_1_true += 1_i * _state_at_pos_flags[idx][q];
        }
        model.add_constraint(move(exactly_1_true) == 1_i);
    }

    // Root: state at layer 0 is the unique root node 0.
    model.add_constraint(WPBSum{} + 1_i * _state_at_pos_flags[0][0] >= 1_i);

    // Final layer: at least one accepting terminal is reached.
    WPBSum accept_sum;
    for (const auto & f : _accepting_terminals)
        accept_sum += 1_i * _state_at_pos_flags[_vars.size()][f];
    model.add_constraint(move(accept_sum) >= 1_i);

    for (size_t idx = 0; idx < _vars.size(); ++idx) {
        for (long q = 0; q < _nodes_per_layer[idx]; ++q) {
            for (const auto & val : _opb_alphabet[idx]) {
                auto new_q = find_transition(_layer_transitions[idx][q], val);
                if (new_q == -1) {
                    // No transition exists for (q, val) at this layer.
                    model.add_constraint(
                        WPBSum{} + 1_i * (_vars[idx] != val) + 1_i * ! _state_at_pos_flags[idx][q] >= 1_i);
                }
                else {
                    model.add_constraint(
                        WPBSum{} + 1_i * ! _state_at_pos_flags[idx][q] + 1_i * (_vars[idx] != val) + 1_i * _state_at_pos_flags[idx + 1][new_q] >= 1_i);
                }
            }
        }
    }
}

auto MDD::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    propagators.install(
        [v = _vars, t = _layer_transitions, npl = _nodes_per_layer, ats = _accepting_terminals,
            g = _graph_idx, flags = move(_state_at_pos_flags)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            propagate_mdd(v, npl, t, ats, flags, g, state, inference, logger);
            return PropagatorState::Enable;
        },
        triggers);
}

auto MDD::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} mdd (", _name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ")\n       (");
    for (const auto & n : _nodes_per_layer)
        print(s, " {}", n);
    print(s, ")\n       ((");
    for (size_t i = 0; i < _layer_transitions.size(); ++i) {
        print(s, "(");
        for (long q = 0; cmp_less(q, _layer_transitions[i].size()); ++q) {
            print(s, "(");
            for (const auto & [val, to] : _layer_transitions[i][q])
                print(s, " ({} {} {})", q, val, to);
            print(s, ")");
        }
        print(s, ")\n        ");
    }
    print(s, "))\n       (");
    for (const auto & f : _accepting_terminals)
        print(s, " {}", f);
    print(s, ")");

    return s.str();
}
