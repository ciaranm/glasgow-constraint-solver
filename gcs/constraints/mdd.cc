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
#include <memory>
#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::any_cast;
using std::cmp_less;
using std::make_shared;
using std::make_unique;
using std::move;
using std::set;
using std::shared_ptr;
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

    // Per-subtree dead-state cache: tracks which `~state[i][q]` proof lines
    // have already been emitted at or above the current search depth, so
    // the per-call propagator skips re-emission. Pre-populated with the
    // statically-dead set (those emitted at Top by the initialiser) so the
    // first per-call sweep doesn't redundantly re-derive them.
    struct DeadCache
    {
        vector<set<long>> dead;
    };

    auto emit_dead_state(ProofLogger * const logger, DeadCache & cache,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        long i, long q, const ReasonFunction & reason) -> void
    {
        if (! logger)
            return;
        if (cache.dead[i].contains(q))
            return;
        logger->emit_rup_proof_line_under_reason(reason,
            WPBSum{} + 1_i * ! state_at_pos_flags[i][q] >= 1_i, ProofLevel::Current);
        cache.dead[i].insert(q);
    }

    auto initialise_graph(MDDGraph & graph, DeadCache & cache, const vector<IntegerVariableID> & vars,
        const vector<long> & nodes_per_layer,
        const vector<vector<unordered_map<Integer, long>>> & layer_transitions,
        const vector<long> & accepting_terminals,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const State & state, const ReasonFunction & reason, ProofLogger * const logger)
    {
        auto num_vars = vars.size();

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

            // Nodes at layer i+1 that aren't forward-reachable under current
            // dom get a single ~state[i+1][next_q] line at Current, gated on
            // the cache. The initialiser's backward chains (Top) plus the
            // cached ~state[i][q] lines for parents we already eliminated at
            // earlier layers let UP close this RUP.
            for (long next_q = 0; next_q < nodes_per_layer[i + 1]; ++next_q) {
                if (graph.nodes[i + 1].contains(next_q)) continue;
                emit_dead_state(logger, cache, state_at_pos_flags, i + 1, next_q, reason);
            }
        }

        // Restrict the final layer to accepting terminals that are also reachable.
        set<long> reachable_accepting;
        for (auto f : accepting_terminals)
            if (graph.nodes[num_vars].contains(f))
                reachable_accepting.insert(f);

        // Non-accepting terminals are statically dead and already covered by
        // the initialiser's Top emission. Anything reachable under current dom
        // but not accepting was already in `cache.dead` from the static set,
        // so emit_dead_state is a no-op here for normal MDDs; we still call it
        // so cases where the static reduction missed something (it shouldn't,
        // but be safe) are covered.
        for (const auto & q : graph.nodes[num_vars])
            if (! reachable_accepting.contains(q))
                emit_dead_state(logger, cache, state_at_pos_flags, num_vars, q, reason);
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
                    }
                }
            }

            set<long> gn = graph.nodes[i];
            for (const auto & q : gn) {
                if (! node_is_support[q]) {
                    graph.nodes[i].erase(q);
                    emit_dead_state(logger, cache, state_at_pos_flags, i, q, reason);
                }
            }
        }

        graph.initialised = true;
    }

    auto decrement_outdeg(MDDGraph & graph, DeadCache & cache, const long i, const long k,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const ReasonFunction & reason, ProofLogger * const logger) -> void
    {
        graph.out_deg[i][k]--;
        if (graph.out_deg[i][k] == 0 && i > 0) {
            for (const auto & edge : graph.in_edges[i][k]) {
                auto l = edge.first;
                graph.out_edges[i - 1][l].erase(k);
                for (const auto & val : edge.second) {
                    graph.nodes_supporting[i - 1][val].erase(l);
                    decrement_outdeg(graph, cache, i - 1, l, state_at_pos_flags, reason, logger);
                }
            }
            graph.in_edges[i][k] = {};
            emit_dead_state(logger, cache, state_at_pos_flags, i, k, reason);
        }
    }

    auto decrement_indeg(MDDGraph & graph, DeadCache & cache, const long i, const long k,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const ReasonFunction & reason, ProofLogger * const logger) -> void
    {
        graph.in_deg[i][k]--;
        if (graph.in_deg[i][k] == 0 && cmp_less(i, graph.in_deg.size() - 1)) {
            emit_dead_state(logger, cache, state_at_pos_flags, i, k, reason);
            for (const auto & edge : graph.out_edges[i][k]) {
                auto l = edge.first;
                graph.in_edges[i + 1][l].erase(k);
                for (const auto & val : edge.second) {
                    graph.nodes_supporting[i][val].erase(k);
                    decrement_indeg(graph, cache, i + 1, l, state_at_pos_flags, reason, logger);
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
        const ConstraintStateHandle & cache_handle,
        const State & state, auto & inference, ProofLogger * const logger) -> void
    {
        auto & graph = any_cast<MDDGraph &>(state.get_constraint_state(graph_handle));
        auto & cache = any_cast<DeadCache &>(state.get_constraint_state(cache_handle));
        auto reason = generic_reason(state, vars);

        if (! graph.initialised)
            initialise_graph(graph, cache, vars, nodes_per_layer, layer_transitions, accepting_terminals,
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

                        decrement_outdeg(graph, cache, i, q, state_at_pos_flags, reason, logger);
                        decrement_indeg(graph, cache, i + 1, next_q, state_at_pos_flags, reason, logger);
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

    // Static forward + backward reachability under initial domains. Returns
    // the per-layer set of dead nodes; the initialiser emits a Top-level
    // ~state[i][q] for each, and pre-populates the per-subtree DeadCache so
    // the per-call propagator never re-emits them.
    auto compute_static_dead(const vector<IntegerVariableID> & vars,
        const vector<long> & nodes_per_layer,
        const vector<vector<unordered_map<Integer, long>>> & layer_transitions,
        const vector<long> & accepting_terminals,
        const State & initial_state) -> vector<set<long>>
    {
        auto num_vars = vars.size();

        // Forward pass: which nodes are reachable from the root under
        // initial domains.
        vector<set<long>> fwd_reachable(num_vars + 1);
        fwd_reachable[0].insert(0);
        for (size_t i = 0; i < num_vars; ++i) {
            for (auto val : initial_state.each_value_immutable(vars[i])) {
                for (auto q : fwd_reachable[i]) {
                    auto next_q = find_transition(layer_transitions[i][q], val);
                    if (next_q != -1)
                        fwd_reachable[i + 1].insert(next_q);
                }
            }
        }

        // Backward pass: from the accepting terminals that are also forward-
        // reachable, walk backward through transitions that stay within
        // fwd_reachable. A node is `bwd_reachable` iff it has at least one
        // path forward to an accepting terminal under initial dom.
        vector<set<long>> bwd_reachable(num_vars + 1);
        for (auto f : accepting_terminals)
            if (fwd_reachable[num_vars].contains(f))
                bwd_reachable[num_vars].insert(f);
        for (long i = static_cast<long>(num_vars) - 1; i >= 0; --i) {
            for (auto q : fwd_reachable[i]) {
                for (auto val : initial_state.each_value_immutable(vars[i])) {
                    auto next_q = find_transition(layer_transitions[i][q], val);
                    if (next_q != -1 && bwd_reachable[i + 1].contains(next_q)) {
                        bwd_reachable[i].insert(q);
                        break;
                    }
                }
            }
        }

        vector<set<long>> dead(num_vars + 1);
        for (size_t i = 0; i <= num_vars; ++i)
            for (long q = 0; q < nodes_per_layer[i]; ++q)
                if (! bwd_reachable[i].contains(q))
                    dead[i].insert(q);
        return dead;
    }

    // Emit the Top-level proof scaffolding once at search root:
    //
    //  1. For every (i, q', val) with val in initial dom, a per-val backward
    //     chain
    //        ~state[i+1][q'] + (vars[i] != val) + sum_{q in parents} state[i][q] >= 1
    //     RUP-derivable from the OPB forward chains plus the per-layer
    //     exactly-one (assume the negation, AMO at layer i+1 forces all other
    //     state[i+1] to 0, layer-i ALO forces some non-parent state[i][q*]=1,
    //     the forward chain for (q*, val) UP-contradicts).
    //
    //  2. ~state[i][q] for every statically dead (forward-unreachable or
    //     backward-unreachable-to-accepting) node, in an order that lets RUP
    //     close: forward-unreachable in layer-ascending order (uses the
    //     backward chains plus earlier-layer dead flags), then everything
    //     left (forward-reachable but no path forward to accepting) in layer-
    //     descending order (uses OPB forward chains plus later-layer dead
    //     flags).
    auto emit_top_scaffolding(ProofLogger * const logger,
        const vector<IntegerVariableID> & vars,
        const vector<long> & nodes_per_layer,
        const vector<vector<unordered_map<Integer, long>>> & layer_transitions,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const State & initial_state,
        const vector<set<long>> & static_dead) -> void
    {
        auto num_vars = vars.size();

        logger->emit_proof_comment("MDD: per-val backward chains");
        for (size_t i = 0; i < num_vars; ++i) {
            for (long next_q = 0; next_q < nodes_per_layer[i + 1]; ++next_q) {
                for (auto val : initial_state.each_value_immutable(vars[i])) {
                    WPBSum chain;
                    chain += 1_i * ! state_at_pos_flags[i + 1][next_q];
                    chain += 1_i * (vars[i] != val);
                    for (long q = 0; q < nodes_per_layer[i]; ++q) {
                        auto succ = find_transition(layer_transitions[i][q], val);
                        if (succ == next_q)
                            chain += 1_i * state_at_pos_flags[i][q];
                    }
                    logger->emit_rup_proof_line(move(chain) >= 1_i, ProofLevel::Top);
                }
            }
        }

        // Forward-unreachable dead nodes, in ascending layer order. RUP for
        // ~state[i][q]: assume state[i][q]=1; for each val in initial dom the
        // backward chain forces ((vars[i-1]!=val) + sum_parents state[i-1])>=1;
        // every q* in parents is forward-unreachable too (q reachable iff
        // some parent reachable) so its ~state[i-1][q*] is already at Top;
        // UP forces (vars[i-1]!=val); var-domain ALO contradicts.
        //
        // Forward-unreachable here means: not reachable from root under
        // initial dom. We can detect that simply by re-running the forward
        // pass — but compute_static_dead already gave us bwd_reachable; the
        // "forward-reachable but not bwd_reachable" nodes are handled by the
        // descending pass below. Layer 0 has no forward-unreachable node
        // (state[0][0]=1 by the root axiom).
        logger->emit_proof_comment("MDD: forward-unreachable static dead nodes");
        vector<set<long>> fwd_reachable(num_vars + 1);
        fwd_reachable[0].insert(0);
        for (size_t i = 0; i < num_vars; ++i) {
            for (auto val : initial_state.each_value_immutable(vars[i])) {
                for (auto q : fwd_reachable[i]) {
                    auto next_q = find_transition(layer_transitions[i][q], val);
                    if (next_q != -1)
                        fwd_reachable[i + 1].insert(next_q);
                }
            }
        }
        for (size_t i = 1; i <= num_vars; ++i) {
            for (long q = 0; q < nodes_per_layer[i]; ++q) {
                if (! fwd_reachable[i].contains(q))
                    logger->emit_rup_proof_line(
                        WPBSum{} + 1_i * ! state_at_pos_flags[i][q] >= 1_i, ProofLevel::Top);
            }
        }

        // Backward-unreachable (forward-reachable but no path forward to an
        // accepting terminal), in descending layer order. RUP for ~state[i][q]:
        // assume state[i][q]=1; for each val in initial dom the OPB forward
        // chain forces ((vars[i]!=val) + state[i+1][succ])>=1; if a transition
        // exists succ is itself backward-unreachable (parent has a path iff
        // some child has), so ~state[i+1][succ] is already at Top, UP forces
        // (vars[i]!=val); if no transition the OPB clause forces it directly;
        // var-domain ALO contradicts.
        //
        // Layer n: handled at the start by emitting ~state[n][q] for every q
        // not in accepting_terminals (they are statically dead, derivable from
        // the per-layer exactly-one plus the at-least-one-accepting axiom).
        logger->emit_proof_comment("MDD: backward-unreachable static dead nodes");
        for (long i = static_cast<long>(num_vars); i >= 0; --i) {
            for (auto q : static_dead[i]) {
                if (i > 0 && ! fwd_reachable[i].contains(q))
                    continue; // already emitted by the forward-unreachable pass
                logger->emit_rup_proof_line(
                    WPBSum{} + 1_i * ! state_at_pos_flags[i][q] >= 1_i, ProofLevel::Top);
            }
        }
    }
}

struct MDD::Bridge
{
    vector<vector<ProofFlag>> state_at_pos_flags;
    vector<set<long>> static_dead;
};

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
    _bridge = make_shared<Bridge>();
    _graph_idx = initial_state.add_constraint_state(MDDGraph(static_cast<long>(_vars.size()), _nodes_per_layer));
    _dead_cache_idx = initial_state.add_constraint_state(
        DeadCache{vector<set<long>>(_nodes_per_layer.size())});

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
    auto & flags = _bridge->state_at_pos_flags;
    for (size_t idx = 0; idx <= _vars.size(); ++idx) {
        WPBSum exactly_1_true{};
        flags.emplace_back();
        for (long q = 0; q < _nodes_per_layer[idx]; ++q) {
            flags[idx].emplace_back(model.create_proof_flag(format("mddnode{}is{}", idx, q)));
            exactly_1_true += 1_i * flags[idx][q];
        }
        model.add_constraint(move(exactly_1_true) == 1_i);
    }

    // Root: state at layer 0 is the unique root node 0.
    model.add_constraint(WPBSum{} + 1_i * flags[0][0] >= 1_i);

    // Final layer: at least one accepting terminal is reached.
    WPBSum accept_sum;
    for (const auto & f : _accepting_terminals)
        accept_sum += 1_i * flags[_vars.size()][f];
    model.add_constraint(move(accept_sum) >= 1_i);

    for (size_t idx = 0; idx < _vars.size(); ++idx) {
        for (long q = 0; q < _nodes_per_layer[idx]; ++q) {
            for (const auto & val : _opb_alphabet[idx]) {
                auto new_q = find_transition(_layer_transitions[idx][q], val);
                if (new_q == -1) {
                    // No transition exists for (q, val) at this layer.
                    model.add_constraint(
                        WPBSum{} + 1_i * (_vars[idx] != val) + 1_i * ! flags[idx][q] >= 1_i);
                }
                else {
                    model.add_constraint(
                        WPBSum{} + 1_i * ! flags[idx][q] + 1_i * (_vars[idx] != val) + 1_i * flags[idx + 1][new_q] >= 1_i);
                }
            }
        }
    }
}

auto MDD::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    // Top-level scaffolding: per-val backward chains and static dead-node
    // lines, derived once from the OPB encoding at search root. Pre-populates
    // the per-subtree DeadCache so the propagator skips re-emission for
    // statically-dead nodes. Without a logger there's nothing to scaffold.
    propagators.install_initialiser(
        [vars = _vars, npl = _nodes_per_layer, t = _layer_transitions, ats = _accepting_terminals,
            bridge = _bridge, dead_cache_handle = _dead_cache_idx](
            State & state, auto &, ProofLogger * const logger) -> void {
            if (! logger)
                return;
            bridge->static_dead = compute_static_dead(vars, npl, t, ats, state);
            emit_top_scaffolding(logger, vars, npl, t, bridge->state_at_pos_flags, state, bridge->static_dead);
            auto & cache = any_cast<DeadCache &>(state.get_constraint_state(dead_cache_handle));
            for (size_t i = 0; i < bridge->static_dead.size(); ++i)
                cache.dead[i].insert(bridge->static_dead[i].begin(), bridge->static_dead[i].end());
        });

    propagators.install(
        [v = _vars, t = _layer_transitions, npl = _nodes_per_layer, ats = _accepting_terminals,
            g = _graph_idx, dc = _dead_cache_idx, bridge = _bridge](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            propagate_mdd(v, npl, t, ats, bridge->state_at_pos_flags, g, dc, state, inference, logger);
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
