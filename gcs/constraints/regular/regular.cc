#include <gcs/constraints/regular/regular.hh>
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
    auto find_transition(const unordered_map<Integer, long> & state_transitions, Integer val) -> long
    {
        auto it = state_transitions.find(val);
        if (it == state_transitions.end())
            return -1L;
        return it->second;
    }

    struct RegularGraph
    {
        // states_supporting[i][val] = states in layer i with an outgoing transition
        // on val that currently sit on a root-to-accepting path.
        vector<unordered_map<Integer, set<long>>> states_supporting;
        // out_edges[i][q] maps target state q' (in layer i+1) to the set of values
        // labelling edges q -> q'.
        vector<vector<unordered_map<long, unordered_set<Integer>>>> out_edges;
        vector<vector<long>> out_deg;
        vector<vector<unordered_map<long, unordered_set<Integer>>>> in_edges;
        vector<vector<long>> in_deg;
        // nodes[i] = active states in layer i.
        vector<set<long>> nodes;
        bool initialised = false;

        explicit RegularGraph(long num_vars, long num_states) :
            states_supporting(num_vars),
            out_edges(num_vars, vector<unordered_map<long, unordered_set<Integer>>>(num_states)),
            out_deg(num_vars, vector<long>(num_states, 0)),
            in_edges(num_vars + 1, vector<unordered_map<long, unordered_set<Integer>>>(num_states)),
            in_deg(num_vars + 1, vector<long>(num_states, 0)),
            nodes(num_vars + 1)
        {
        }
    };

    // Per-subtree dead-state cache: tracks which `~state[i][q]` proof lines
    // have already been emitted at or above the current search depth, so the
    // per-call propagator skips re-emission. Pre-populated with the
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

    auto initialise_graph(RegularGraph & graph, DeadCache & cache, const vector<IntegerVariableID> & vars,
        const long num_states, const vector<unordered_map<Integer, long>> & transitions,
        const vector<long> & final_states,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const State & state, const ReasonFunction & reason, ProofLogger * const logger)
    {
        auto num_vars = vars.size();

        // Forward phase: states reachable from the root under current domains.
        graph.nodes[0].insert(0);
        for (size_t i = 0; i < num_vars; ++i) {
            for (auto val : state.each_value_immutable(vars[i])) {
                for (const auto & q : graph.nodes[i]) {
                    auto next_q = find_transition(transitions[q], val);
                    if (next_q != -1) {
                        graph.states_supporting[i][val].insert(q);
                        graph.nodes[i + 1].insert(next_q);
                    }
                }
            }

            // States at layer i+1 that aren't forward-reachable under current
            // dom get a single ~state[i+1][next_q] line at Current, gated on
            // the cache. The initialiser's backward chains (Top) plus the
            // cached ~state[i][q] lines for parents we already eliminated at
            // earlier layers let UP close this RUP.
            for (long next_q = 0; next_q < num_states; ++next_q) {
                if (graph.nodes[i + 1].contains(next_q)) continue;
                emit_dead_state(logger, cache, state_at_pos_flags, static_cast<long>(i) + 1, next_q, reason);
            }
        }

        // Restrict the final layer to final states that are also reachable.
        set<long> reachable_final;
        for (auto f : final_states)
            if (graph.nodes[num_vars].contains(f))
                reachable_final.insert(f);

        // Anything reachable under current dom but not in final_states was
        // already in cache.dead from the static set, so emit_dead_state is a
        // no-op here for well-formed DFAs.
        for (const auto & q : graph.nodes[num_vars])
            if (! reachable_final.contains(q))
                emit_dead_state(logger, cache, state_at_pos_flags, static_cast<long>(num_vars), q, reason);
        graph.nodes[num_vars] = reachable_final;

        // Backward phase: drop states with no path forward to a final state.
        for (long i = static_cast<long>(num_vars) - 1; i >= 0; --i) {
            vector<char> state_is_support(num_states, 0);

            for (auto val : state.each_value_mutable(vars[i])) {
                set<long> states = graph.states_supporting[i][val];
                for (const auto & q : states) {
                    auto next_q = find_transition(transitions[q], val);
                    if (next_q != -1 && graph.nodes[i + 1].contains(next_q)) {
                        graph.out_edges[i][q][next_q].emplace(val);
                        graph.out_deg[i][q]++;
                        graph.in_edges[i + 1][next_q][q].emplace(val);
                        graph.in_deg[i + 1][next_q]++;
                        state_is_support[q] = 1;
                    }
                    else {
                        graph.states_supporting[i][val].erase(q);
                    }
                }
            }

            set<long> gn = graph.nodes[i];
            for (const auto & q : gn) {
                if (! state_is_support[q]) {
                    graph.nodes[i].erase(q);
                    emit_dead_state(logger, cache, state_at_pos_flags, i, q, reason);
                }
            }
        }

        graph.initialised = true;
    }

    auto decrement_outdeg(RegularGraph & graph, DeadCache & cache, const long i, const long k,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const ReasonFunction & reason, ProofLogger * const logger) -> void
    {
        graph.out_deg[i][k]--;
        if (graph.out_deg[i][k] == 0 && i > 0) {
            for (const auto & edge : graph.in_edges[i][k]) {
                auto l = edge.first;
                graph.out_edges[i - 1][l].erase(k);
                for (const auto & val : edge.second) {
                    graph.states_supporting[i - 1][val].erase(l);
                    decrement_outdeg(graph, cache, i - 1, l, state_at_pos_flags, reason, logger);
                }
            }
            graph.in_edges[i][k] = {};
            emit_dead_state(logger, cache, state_at_pos_flags, i, k, reason);
        }
    }

    auto decrement_indeg(RegularGraph & graph, DeadCache & cache, const long i, const long k,
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
                    graph.states_supporting[i][val].erase(k);
                    decrement_indeg(graph, cache, i + 1, l, state_at_pos_flags, reason, logger);
                }
            }
            graph.out_edges[i][k] = {};
        }
    }

    auto propagate_regular(const vector<IntegerVariableID> & vars,
        const long num_states,
        const vector<unordered_map<Integer, long>> & transitions,
        const vector<long> & final_states,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const ConstraintStateHandle & graph_handle,
        const ConstraintStateHandle & cache_handle,
        const State & state, auto & inference, ProofLogger * const logger) -> void
    {
        auto & graph = any_cast<RegularGraph &>(state.get_constraint_state(graph_handle));
        auto & cache = any_cast<DeadCache &>(state.get_constraint_state(cache_handle));
        auto reason = generic_reason(state, vars);

        if (! graph.initialised)
            initialise_graph(graph, cache, vars, num_states, transitions, final_states,
                state_at_pos_flags, state, reason, logger);

        for (size_t i = 0; i < graph.states_supporting.size(); ++i) {
            for (const auto & val_and_states : graph.states_supporting[i]) {
                auto val = val_and_states.first;

                if (! graph.states_supporting[i][val].empty() && ! state.in_domain(vars[i], val)) {
                    for (const auto & q : graph.states_supporting[i][val]) {
                        auto next_q = find_transition(transitions[q], val);

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

                        decrement_outdeg(graph, cache, static_cast<long>(i), q, state_at_pos_flags, reason, logger);
                        decrement_indeg(graph, cache, static_cast<long>(i) + 1, next_q, state_at_pos_flags, reason, logger);
                    }
                    graph.states_supporting[i][val] = {};
                }
            }
        }

        for (size_t i = 0; i < graph.states_supporting.size(); ++i) {
            for (auto val : state.each_value_mutable(vars[i])) {
                if (graph.states_supporting[i][val].empty())
                    inference.infer_not_equal(logger, vars[i], val, JustifyUsingRUP{}, reason);
            }
        }
    }

    // Static forward + backward reachability under initial domains. Returns
    // the per-layer set of dead states; the initialiser emits a Top-level
    // ~state[i][q] for each, and pre-populates the per-subtree DeadCache so
    // the per-call propagator never re-emits them.
    auto compute_static_dead(const vector<IntegerVariableID> & vars,
        const long num_states,
        const vector<unordered_map<Integer, long>> & transitions,
        const vector<long> & final_states,
        const State & initial_state) -> vector<set<long>>
    {
        auto num_vars = vars.size();

        vector<set<long>> fwd_reachable(num_vars + 1);
        fwd_reachable[0].insert(0);
        for (size_t i = 0; i < num_vars; ++i) {
            for (auto val : initial_state.each_value_immutable(vars[i])) {
                for (auto q : fwd_reachable[i]) {
                    auto next_q = find_transition(transitions[q], val);
                    if (next_q != -1)
                        fwd_reachable[i + 1].insert(next_q);
                }
            }
        }

        vector<set<long>> bwd_reachable(num_vars + 1);
        for (auto f : final_states)
            if (fwd_reachable[num_vars].contains(f))
                bwd_reachable[num_vars].insert(f);
        for (long i = static_cast<long>(num_vars) - 1; i >= 0; --i) {
            for (auto q : fwd_reachable[i]) {
                for (auto val : initial_state.each_value_immutable(vars[i])) {
                    auto next_q = find_transition(transitions[q], val);
                    if (next_q != -1 && bwd_reachable[i + 1].contains(next_q)) {
                        bwd_reachable[i].insert(q);
                        break;
                    }
                }
            }
        }

        vector<set<long>> dead(num_vars + 1);
        for (size_t i = 0; i <= num_vars; ++i)
            for (long q = 0; q < num_states; ++q)
                if (! bwd_reachable[i].contains(q))
                    dead[i].insert(q);
        return dead;
    }

    // Emit the Top-level proof scaffolding once at search root:
    //
    //  1. For every (i, q', val) with val in initial dom, a per-val backward
    //     chain
    //        ~state[i+1][q'] + (vars[i] != val) + sum_{q : T(q,val) = q'} state[i][q] >= 1
    //     RUP-derivable from the OPB forward chains plus the per-layer
    //     exactly-one (assume the negation, AMO at layer i+1 forces all other
    //     state[i+1] to 0, layer-i ALO forces some non-parent state[i][q*]=1,
    //     the forward chain for (q*, val) UP-contradicts).
    //
    //  2. ~state[i][q] for every statically dead (forward-unreachable or
    //     backward-unreachable-to-accepting) state, in an order that lets RUP
    //     close: forward-unreachable in layer-ascending order (uses the
    //     backward chains plus earlier-layer dead flags), then everything
    //     left (forward-reachable but no path forward to a final state) in
    //     descending layer order (uses OPB forward chains plus later-layer
    //     dead flags).
    auto emit_top_scaffolding(ProofLogger * const logger,
        const vector<IntegerVariableID> & vars,
        const long num_states,
        const vector<unordered_map<Integer, long>> & transitions,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const State & initial_state,
        const vector<set<long>> & static_dead) -> void
    {
        auto num_vars = vars.size();

        logger->emit_proof_comment("Regular: per-val backward chains");
        for (size_t i = 0; i < num_vars; ++i) {
            for (long next_q = 0; next_q < num_states; ++next_q) {
                for (auto val : initial_state.each_value_immutable(vars[i])) {
                    WPBSum chain;
                    chain += 1_i * ! state_at_pos_flags[i + 1][next_q];
                    chain += 1_i * (vars[i] != val);
                    for (long q = 0; q < num_states; ++q) {
                        auto succ = find_transition(transitions[q], val);
                        if (succ == next_q)
                            chain += 1_i * state_at_pos_flags[i][q];
                    }
                    logger->emit_rup_proof_line(move(chain) >= 1_i, ProofLevel::Top);
                }
            }
        }

        // Forward-unreachable static dead states, in ascending layer order.
        logger->emit_proof_comment("Regular: forward-unreachable static dead states");
        vector<set<long>> fwd_reachable(num_vars + 1);
        fwd_reachable[0].insert(0);
        for (size_t i = 0; i < num_vars; ++i) {
            for (auto val : initial_state.each_value_immutable(vars[i])) {
                for (auto q : fwd_reachable[i]) {
                    auto next_q = find_transition(transitions[q], val);
                    if (next_q != -1)
                        fwd_reachable[i + 1].insert(next_q);
                }
            }
        }
        for (size_t i = 1; i <= num_vars; ++i) {
            for (long q = 0; q < num_states; ++q) {
                if (! fwd_reachable[i].contains(q))
                    logger->emit_rup_proof_line(
                        WPBSum{} + 1_i * ! state_at_pos_flags[i][q] >= 1_i, ProofLevel::Top);
            }
        }

        // Backward-unreachable (forward-reachable but no path forward to a
        // final state), in descending layer order.
        logger->emit_proof_comment("Regular: backward-unreachable static dead states");
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

struct Regular::Bridge
{
    vector<vector<ProofFlag>> state_at_pos_flags;
    vector<set<long>> static_dead;
};

Regular::Regular(vector<IntegerVariableID> v, long n, vector<unordered_map<Integer, long>> t, vector<long> f, bool sr) :
    _vars(move(v)),
    _num_states(n),
    _transitions(move(t)),
    _final_states(move(f)),
    _short_reasons(sr)
{
    set<Integer> sym_set;
    for (const auto & state_map : _transitions)
        for (const auto & [val, _] : state_map)
            sym_set.insert(val);
    _symbols.assign(sym_set.begin(), sym_set.end());
}

Regular::Regular(vector<IntegerVariableID> v, long n, vector<vector<long>> transitions, vector<long> f, bool sr) :
    _vars(move(v)),
    _num_states(n),
    _transitions(vector<unordered_map<Integer, long>>(n, unordered_map<Integer, long>{})),
    _final_states(move(f)),
    _short_reasons(sr)
{
    for (size_t i = 0; i < transitions.size(); ++i)
        for (size_t j = 0; j < transitions[i].size(); ++j)
            if (transitions[i][j] != -1)
                _transitions[i][Integer(j)] = transitions[i][j];
    set<Integer> sym_set;
    for (const auto & state_map : _transitions)
        for (const auto & [val, _] : state_map)
            sym_set.insert(val);
    _symbols.assign(sym_set.begin(), sym_set.end());
}

auto Regular::symbols() const -> const vector<Integer> &
{
    return _symbols;
}

auto Regular::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Regular>(_vars, _num_states, _transitions, _final_states, _short_reasons);
}

auto Regular::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Regular::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    _bridge = make_shared<Bridge>();
    _graph_idx = initial_state.add_constraint_state(RegularGraph(static_cast<long>(_vars.size()), _num_states));
    _dead_cache_idx = initial_state.add_constraint_state(
        DeadCache{vector<set<long>>(_vars.size() + 1)});

    // OPB alphabet: union of transition keys and every variable's initial
    // domain. Domain values absent from every transition get a
    // "no-transition" constraint emitted in define_proof_model, which is
    // what veripb needs to verify the propagator's RUP-justified pruning of
    // those values.
    _opb_alphabet.insert(_symbols.begin(), _symbols.end());
    for (const auto & var : _vars)
        for (const auto & val : initial_state.each_value_immutable(var))
            _opb_alphabet.insert(val);

    return true;
}

auto Regular::define_proof_model(ProofModel & model) -> void
{
    // state_at_pos_flags[i][q] means "after reading the first i symbols, the
    // DFA is in state q". Layer i takes input vars[i] and produces layer
    // i+1.
    auto & flags = _bridge->state_at_pos_flags;
    for (size_t idx = 0; idx <= _vars.size(); ++idx) {
        WPBSum exactly_1_true{};
        flags.emplace_back();
        for (long q = 0; q < _num_states; ++q) {
            flags[idx].emplace_back(model.create_proof_flag(format("state{}is{}", idx, q)));
            exactly_1_true += 1_i * flags[idx][q];
        }
        model.add_constraint(move(exactly_1_true) == 1_i);
    }

    // Root: state at layer 0 is the start state 0.
    model.add_constraint(WPBSum{} + 1_i * flags[0][0] >= 1_i);

    // Final layer: at least one final state is reached.
    WPBSum pos_n_states;
    for (const auto & f : _final_states)
        pos_n_states += 1_i * flags[_vars.size()][f];
    model.add_constraint(move(pos_n_states) >= 1_i);

    for (size_t idx = 0; idx < _vars.size(); ++idx) {
        for (long q = 0; q < _num_states; ++q) {
            for (const auto & val : _opb_alphabet) {
                auto new_q = find_transition(_transitions[q], val);
                if (new_q == -1) {
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

auto Regular::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    // Top-level scaffolding: per-val backward chains and static dead-state
    // lines, derived once from the OPB encoding at search root. Pre-populates
    // the per-subtree DeadCache so the propagator skips re-emission for
    // statically-dead states. Without a logger there's nothing to scaffold.
    propagators.install_initialiser(
        [vars = _vars, ns = _num_states, t = _transitions, fs = _final_states,
            bridge = _bridge, dead_cache_handle = _dead_cache_idx](
            State & state, auto &, ProofLogger * const logger) -> void {
            if (! logger)
                return;
            bridge->static_dead = compute_static_dead(vars, ns, t, fs, state);
            emit_top_scaffolding(logger, vars, ns, t, bridge->state_at_pos_flags, state, bridge->static_dead);
            auto & cache = any_cast<DeadCache &>(state.get_constraint_state(dead_cache_handle));
            for (size_t i = 0; i < bridge->static_dead.size(); ++i)
                cache.dead[i].insert(bridge->static_dead[i].begin(), bridge->static_dead[i].end());
        });

    propagators.install(
        [v = _vars, ns = _num_states, t = _transitions, fs = _final_states,
            g = _graph_idx, dc = _dead_cache_idx, bridge = _bridge](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            propagate_regular(v, ns, t, fs, bridge->state_at_pos_flags, g, dc, state, inference, logger);
            return PropagatorState::Enable;
        },
        triggers);
}

auto Regular::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} regular (", _name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") {}\n       (", _num_states);
    for (const auto & sym : symbols())
        print(s, " {}", sym);
    print(s, ")\n       ((");
    for (size_t i = 0; i < _transitions.size(); ++i) {
        print(s, "(");
        for (const auto & tran : _transitions[i]) {
            print(s, " ({} {})", tran.first, tran.second);
        }
        print(s, ")\n        ");
    }
    print(s, "))\n       (");
    for (const auto & f : _final_states)
        print(s, " {}", f);
    print(s, ")");

    return s.str();
}
