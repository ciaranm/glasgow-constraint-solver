#include <gcs/constraints/regular/hints.hh>
#include <gcs/constraints/regular/regex.hh>
#include <gcs/constraints/regular/regular.hh>
#include <gcs/constraints/regular/regular_bacchus.hh>
#include <gcs/constraints/regular/regular_legacy.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/proof.hh>

#include <util/overloaded.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <any>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::any_cast;
using std::cmp_less;
using std::make_shared;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::shared_ptr;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

namespace
{
    // Returns the set of next states for (state, val), or an empty set if no
    // transition exists. A deterministic automaton is the special case where
    // every non-empty set is a singleton.
    auto find_transitions(const unordered_map<Integer, set<long>> & state_transitions, Integer val) -> const set<long> &
    {
        static const set<long> none;
        auto it = state_transitions.find(val);
        if (it == state_transitions.end())
            return none;
        return it->second;
    }

    // Records the alphabet (sorted transition keys) for proof logging and s_expr.
    auto symbols_of(const vector<unordered_map<Integer, set<long>>> & transitions) -> vector<Integer>
    {
        set<Integer> sym_set;
        for (const auto & state_map : transitions)
            for (const auto & [val, _] : state_map)
                sym_set.insert(val);
        return {sym_set.begin(), sym_set.end()};
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
            states_supporting(vector<unordered_map<Integer, set<long>>>(num_vars)),
            out_edges(vector<vector<unordered_map<long, unordered_set<Integer>>>>(
                num_vars, vector<unordered_map<long, unordered_set<Integer>>>(num_states))),
            out_deg(vector<vector<long>>(num_vars, vector<long>(num_states, 0))),
            in_edges(vector<vector<unordered_map<long, unordered_set<Integer>>>>(
                num_vars + 1, vector<unordered_map<long, unordered_set<Integer>>>(num_states))),
            in_deg(vector<vector<long>>(num_vars + 1, vector<long>(num_states, 0))), nodes(vector<set<long>>(num_vars + 1))
        {
        }
    };

    // Per-subtree dead-state cache: tracks which `~state[i][q]` proof lines have
    // already been emitted at or above the current search depth, so the per-call
    // propagator skips re-emission. Pre-populated with the statically-dead set
    // (those emitted at Top by the initialiser) so the first per-call sweep
    // doesn't redundantly re-derive them.
    struct DeadCache
    {
        vector<set<long>> dead;
    };

    auto emit_dead_state(ProofLogger * const logger, DeadCache & cache, const vector<vector<ProofFlag>> & state_at_pos_flags, long i, long q,
        const ReasonLiterals & reason) -> void
    {
        if (! logger || logger->get_assertion_level() != AssertionLevel::Off)
            return;
        if (cache.dead[i].contains(q))
            return;
        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * ! state_at_pos_flags[i][q] >= 1_i, ProofLevel::Current);
        cache.dead[i].insert(q);
    }

    // True if state l at position pos still has a live out-edge labelled val. For
    // a DFA this is never the case once the single (l, val) edge is gone, but an
    // NFA may have several edges on the same value.
    auto still_supports(const RegularGraph & graph, const long pos, const long l, Integer val) -> bool
    {
        for (const auto & [next_q, vals] : graph.out_edges[pos][l])
            if (vals.contains(val))
                return true;
        return false;
    }

    auto initialise_graph(RegularGraph & graph, DeadCache & cache, const vector<IntegerVariableID> & vars, const long num_states,
        const vector<unordered_map<Integer, set<long>>> & transitions, const vector<long> & final_states,
        const vector<vector<ProofFlag>> & state_at_pos_flags, const State & state, const ReasonLiterals & reason, ProofLogger * const logger)
    {
        auto num_vars = vars.size();

        // Forward phase: states reachable from the root under current domains.
        graph.nodes[0].insert(0);
        for (size_t i = 0; i < num_vars; ++i) {
            for (auto val : state.each_value_immutable(vars[i])) {
                for (const auto & q : graph.nodes[i]) {
                    const auto & next_states = find_transitions(transitions[q], val);
                    if (! next_states.empty()) {
                        graph.states_supporting[i][val].insert(q);
                        for (const auto & next_q : next_states)
                            graph.nodes[i + 1].insert(next_q);
                    }
                }
            }

            // States at layer i+1 not forward-reachable under current dom get a
            // single ~state[i+1][next_q] line at Current, gated on the cache. The
            // initialiser's Top backward chains plus the cached ~state[i][q] lines
            // for parents eliminated at earlier layers let UP close this RUP.
            for (long next_q = 0; next_q < num_states; ++next_q) {
                if (graph.nodes[i + 1].contains(next_q))
                    continue;
                emit_dead_state(logger, cache, state_at_pos_flags, static_cast<long>(i) + 1, next_q, reason);
            }
        }

        // Restrict the final layer to final states that are also reachable.
        set<long> reachable_final;
        for (auto f : final_states)
            if (graph.nodes[num_vars].contains(f))
                reachable_final.insert(f);

        // Anything reachable under current dom but not in final_states is already
        // in cache.dead from the static set, so emit_dead_state is a no-op here
        // for well-formed automata.
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
                    bool any_live_target = false;
                    for (const auto & next_q : find_transitions(transitions[q], val)) {
                        if (graph.nodes[i + 1].contains(next_q)) {
                            graph.out_edges[i][q][next_q].emplace(val);
                            graph.out_deg[i][q]++;
                            graph.in_edges[i + 1][next_q][q].emplace(val);
                            graph.in_deg[i + 1][next_q]++;
                            any_live_target = true;
                        }
                    }
                    if (any_live_target)
                        state_is_support[q] = 1;
                    else
                        graph.states_supporting[i][val].erase(q);
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

    auto decrement_outdeg(RegularGraph & graph, DeadCache & cache, const long i, const long k, const vector<vector<ProofFlag>> & state_at_pos_flags,
        const ReasonLiterals & reason, ProofLogger * const logger) -> void
    {
        graph.out_deg[i][k]--;
        if (graph.out_deg[i][k] == 0 && i > 0) {
            // Emit before recursing to parents at i-1: ~state[i-1][l]'s RUP
            // (when l's out_deg also hits 0 in the recursion) consumes the
            // forward chain `state[i-1][l] ∧ x[i-1]=val → state[i][T(l,val)]`
            // together with ~state[i][T(l,val)], so all dead children at
            // layer i must be in the proof DB before any layer-(i-1) parent
            // is derived. emit_dead_state is cache-gated, so the recursion
            // can still reach this node without re-emission.
            emit_dead_state(logger, cache, state_at_pos_flags, i, k, reason);
            for (const auto & edge : graph.in_edges[i][k]) {
                auto l = edge.first;
                graph.out_edges[i - 1][l].erase(k);
                for (const auto & val : edge.second) {
                    // For an NFA, l may still reach a live state on val via
                    // another edge; only drop support once no such edge remains.
                    if (! still_supports(graph, i - 1, l, val))
                        graph.states_supporting[i - 1][val].erase(l);
                    decrement_outdeg(graph, cache, i - 1, l, state_at_pos_flags, reason, logger);
                }
            }
            graph.in_edges[i][k] = {};
        }
    }

    auto decrement_indeg(RegularGraph & graph, DeadCache & cache, const long i, const long k, const vector<vector<ProofFlag>> & state_at_pos_flags,
        const ReasonLiterals & reason, ProofLogger * const logger) -> void
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

    auto propagate_regular(const vector<IntegerVariableID> & vars, const long num_states,
        const vector<unordered_map<Integer, set<long>>> & transitions, const vector<long> & final_states,
        const vector<vector<ProofFlag>> & state_at_pos_flags, const ConstraintStateHandle & graph_handle, const ConstraintStateHandle & cache_handle,
        const State & state, auto & inference, ProofLogger * const logger, const ConstraintID & owner, const Reason & reason) -> void
    {
        // Degenerate empty sequence (issue #254): with no variables there is
        // nothing to propagate over, but the empty word is accepted only if the
        // initial state (0) is itself a final state. The proof model pins
        // state_at_pos[0] to state 0 and requires it to be final, so the
        // contradiction is reverse-unit-propagatable.
        if (vars.empty()) {
            bool initial_is_final = false;
            for (auto f : final_states)
                if (f == 0L) {
                    initial_is_final = true;
                    break;
                }
            if (! initial_is_final)
                inference.contradiction(logger, JustifyUsingRUP{hints::Regular{owner}}, reason);
            return;
        }

        auto & graph = any_cast<RegularGraph &>(state.get_constraint_state(graph_handle));
        auto & cache = any_cast<DeadCache &>(state.get_constraint_state(cache_handle));
        // All manual proof emission happens before any domain change below, so a
        // single materialised snapshot is sound (see MDD, PORTING-NOTES §13).
        auto eager = eager_reason(reason, state);

        if (! graph.initialised)
            initialise_graph(graph, cache, vars, num_states, transitions, final_states, state_at_pos_flags, state, eager, logger);

        for (size_t i = 0; i < graph.states_supporting.size(); ++i) {
            for (const auto & val_and_states : graph.states_supporting[i]) {
                auto val = val_and_states.first;

                if (! graph.states_supporting[i][val].empty() && ! state.in_domain(vars[i], val)) {
                    for (const auto & q : graph.states_supporting[i][val]) {
                        // Remove every edge out of q that carries this value; an
                        // NFA may have several. Collect them first to avoid
                        // mutating out_edges[i][q] while iterating it.
                        vector<long> next_qs;
                        for (const auto & [next_q, vals] : graph.out_edges[i][q])
                            if (vals.contains(val))
                                next_qs.push_back(next_q);

                        for (const auto & next_q : next_qs) {
                            graph.out_edges[i][q][next_q].erase(val);
                            if (graph.out_edges[i][q][next_q].empty())
                                graph.out_edges[i][q].erase(next_q);

                            if (graph.in_edges[i + 1][next_q].contains(q)) {
                                graph.in_edges[i + 1][next_q][q].erase(val);
                                if (graph.in_edges[i + 1][next_q][q].empty())
                                    graph.in_edges[i + 1][next_q].erase(q);
                            }

                            decrement_outdeg(graph, cache, static_cast<long>(i), q, state_at_pos_flags, eager, logger);
                            decrement_indeg(graph, cache, static_cast<long>(i) + 1, next_q, state_at_pos_flags, eager, logger);
                        }
                    }
                    graph.states_supporting[i][val] = {};
                }
            }
        }

        for (size_t i = 0; i < graph.states_supporting.size(); ++i) {
            for (auto val : state.each_value_mutable(vars[i])) {
                if (graph.states_supporting[i][val].empty())
                    inference.infer_not_equal(logger, vars[i], val, JustifyUsingRUP{hints::Regular{owner}}, reason);
            }
        }
    }

    // Static forward + backward reachability under initial domains. Returns the
    // per-layer set of dead states; the initialiser emits a Top-level
    // ~state[i][q] for each, and pre-populates the per-subtree DeadCache so the
    // per-call propagator never re-emits them.
    auto compute_static_dead(const vector<IntegerVariableID> & vars, const long num_states,
        const vector<unordered_map<Integer, set<long>>> & transitions, const vector<long> & final_states, const State & initial_state)
        -> vector<set<long>>
    {
        auto num_vars = vars.size();

        vector<set<long>> fwd_reachable(num_vars + 1);
        fwd_reachable[0].insert(0);
        for (size_t i = 0; i < num_vars; ++i)
            for (auto val : initial_state.each_value_immutable(vars[i]))
                for (auto q : fwd_reachable[i])
                    for (auto next_q : find_transitions(transitions[q], val))
                        fwd_reachable[i + 1].insert(next_q);

        vector<set<long>> bwd_reachable(num_vars + 1);
        for (auto f : final_states)
            if (fwd_reachable[num_vars].contains(f))
                bwd_reachable[num_vars].insert(f);
        for (long i = static_cast<long>(num_vars) - 1; i >= 0; --i)
            for (auto q : fwd_reachable[i]) {
                bool found = false;
                for (auto val : initial_state.each_value_immutable(vars[i])) {
                    for (auto next_q : find_transitions(transitions[q], val))
                        if (bwd_reachable[i + 1].contains(next_q)) {
                            bwd_reachable[i].insert(q);
                            found = true;
                            break;
                        }
                    if (found)
                        break;
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
    //        ~state[i+1][q'] + (vars[i] != val) + sum_{q : q' in T(q,val)} state[i][q] >= 1
    //     RUP-derivable from the OPB forward chains plus the per-layer
    //     exactly-one (assume the negation, at-most-one at layer i+1 forces all
    //     other state[i+1] to 0, layer-i at-least-one forces some non-parent
    //     state[i][q*]=1, the forward chain for (q*, val) UP-contradicts because
    //     none of q*'s targets on val is q').
    //
    //  2. ~state[i][q] for every statically dead (forward-unreachable or
    //     backward-unreachable-to-accepting) state, in an order that lets RUP
    //     close: forward-unreachable in layer-ascending order (uses the backward
    //     chains plus earlier-layer dead flags), then everything left in
    //     descending layer order (uses OPB forward chains plus later-layer dead
    //     flags).
    auto emit_top_scaffolding(ProofLogger * const logger, const vector<IntegerVariableID> & vars, const long num_states,
        const vector<unordered_map<Integer, set<long>>> & transitions, const vector<vector<ProofFlag>> & state_at_pos_flags,
        const State & initial_state, const vector<set<long>> & static_dead) -> void
    {
        auto num_vars = vars.size();

        logger->emit_proof_comment("Regular: per-val backward chains");
        for (size_t i = 0; i < num_vars; ++i) {
            for (long next_q = 0; next_q < num_states; ++next_q) {
                for (auto val : initial_state.each_value_immutable(vars[i])) {
                    WPBSum chain;
                    chain += 1_i * ! state_at_pos_flags[i + 1][next_q];
                    chain += 1_i * (vars[i] != val);
                    for (long q = 0; q < num_states; ++q)
                        if (find_transitions(transitions[q], val).contains(next_q))
                            chain += 1_i * state_at_pos_flags[i][q];
                    logger->emit_rup_proof_line(move(chain) >= 1_i, ProofLevel::Top);
                }
            }
        }

        // Forward-unreachable static dead states, in ascending layer order.
        logger->emit_proof_comment("Regular: forward-unreachable static dead states");
        vector<set<long>> fwd_reachable(num_vars + 1);
        fwd_reachable[0].insert(0);
        for (size_t i = 0; i < num_vars; ++i)
            for (auto val : initial_state.each_value_immutable(vars[i]))
                for (auto q : fwd_reachable[i])
                    for (auto next_q : find_transitions(transitions[q], val))
                        fwd_reachable[i + 1].insert(next_q);
        for (size_t i = 1; i <= num_vars; ++i)
            for (long q = 0; q < num_states; ++q)
                if (! fwd_reachable[i].contains(q))
                    logger->emit_rup_proof_line(WPBSum{} + 1_i * ! state_at_pos_flags[i][q] >= 1_i, ProofLevel::Top);

        // Backward-unreachable (forward-reachable but no path forward to a final
        // state), in descending layer order.
        logger->emit_proof_comment("Regular: backward-unreachable static dead states");
        for (long i = static_cast<long>(num_vars); i >= 0; --i)
            for (auto q : static_dead[i]) {
                if (i > 0 && ! fwd_reachable[i].contains(q))
                    continue; // already emitted by the forward-unreachable pass
                logger->emit_rup_proof_line(WPBSum{} + 1_i * ! state_at_pos_flags[i][q] >= 1_i, ProofLevel::Top);
            }
    }
}

struct Regular::Bridge
{
    vector<vector<ProofFlag>> state_at_pos_flags;
    vector<set<long>> static_dead;
};

Regular::Regular(vector<IntegerVariableID> v, long n, vector<unordered_map<Integer, long>> t, vector<long> f) :
    _vars(move(v)), _num_states(n), _transitions(t.size()), _final_states(move(f)), _regex(nullopt)
{
    for (size_t q = 0; q < t.size(); ++q)
        for (const auto & [val, target] : t[q])
            if (target != -1L)
                _transitions[q][val].insert(target);
    _symbols = symbols_of(_transitions);
}

Regular::Regular(vector<IntegerVariableID> v, long n, vector<vector<long>> transitions, vector<long> f) :
    _vars(move(v)), _num_states(n), _transitions(n), _final_states(move(f)), _regex(nullopt)
{
    for (size_t i = 0; i < transitions.size(); ++i)
        for (size_t j = 0; j < transitions[i].size(); ++j)
            if (transitions[i][j] != -1L)
                _transitions[i][Integer(j)].insert(transitions[i][j]);
    _symbols = symbols_of(_transitions);
}

Regular::Regular(vector<IntegerVariableID> v, string regex) : _vars(move(v)), _num_states(0), _regex(move(regex))
{
    // The automaton is compiled from the regex in prepare(), once the
    // variables' domains (and hence the alphabet for "." and "[^...]") are known.
}

Regular::Regular(vector<IntegerVariableID> v, long n, vector<unordered_map<Integer, set<long>>> t, vector<long> f, vector<Integer> syms, bool sr,
    optional<string> regex) :
    _vars(move(v)), _num_states(n), _transitions(move(t)), _final_states(move(f)), _short_reasons(sr), _regex(move(regex)), _symbols(move(syms))
{
}

auto Regular::with_short_reasons(std::optional<bool> short_reasons) -> Regular &
{
    _short_reasons = short_reasons.value_or(true);
    return *this;
}

auto Regular::with_proof_strategy(RegularProofStrategy strategy) -> Regular &
{
    _proof_strategy = strategy;
    return *this;
}

auto Regular::clone() const -> unique_ptr<Constraint>
{
    auto cloned = unique_ptr<Regular>(new Regular(_vars, _num_states, _transitions, _final_states, _symbols, _short_reasons, _regex));
    cloned->with_proof_strategy(_proof_strategy);
    return cloned;
}

auto Regular::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    // The three strategies share this constraint's OPB encoding and its
    // inferences; they differ only in the proof scaffolding, so each is a
    // distinct install path over the same automaton. Upfront is this class's
    // own path; PerCall and Bacchus delegate to the sibling implementations,
    // which are internal to this constraint (not part of the public API).
    overloaded{[&](const proof_strategy::Upfront &) {
                   if (! prepare(propagators, initial_state, optional_model))
                       return;
                   if (optional_model)
                       define_proof_model(*optional_model);
                   install_propagators(propagators);
               },
        [&](const proof_strategy::PerCall &) {
            RegularLegacy legacy{_vars, _num_states, _transitions, _final_states, _symbols, _short_reasons, _regex};
            legacy.set_constraint_id(constraint_id());
            move(legacy).install(propagators, initial_state, optional_model);
        },
        [&](const proof_strategy::Bacchus &) {
            if (_regex)
                throw UnimplementedException{"the Bacchus proof strategy for Regular does not support regular-expression / NFA input"};
            // Recover the deterministic transition map the Bacchus encoding
            // needs from the shared (possibly non-deterministic) representation.
            vector<unordered_map<Integer, long>> dfa(_transitions.size());
            for (size_t q = 0; q < _transitions.size(); ++q)
                for (const auto & [val, targets] : _transitions[q]) {
                    if (targets.size() != 1)
                        throw UnimplementedException{"the Bacchus proof strategy for Regular requires a deterministic automaton"};
                    dfa[q][val] = *targets.begin();
                }
            RegularBacchus bacchus{_vars, _num_states, dfa, _final_states, _short_reasons};
            bacchus.set_constraint_id(constraint_id());
            move(bacchus).install(propagators, initial_state, optional_model);
        }}
        .visit(_proof_strategy);
}

auto Regular::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    if (_regex) {
        // Alphabet for "." and "[^...]": the contiguous min..max range over the
        // union of the variables' domains, mirroring MiniZinc's semantics.
        auto lo = Integer::max_value(), hi = Integer::min_value();
        for (const auto & var : _vars)
            for (const auto & val : initial_state.each_value_immutable(var)) {
                if (val < lo)
                    lo = val;
                if (val > hi)
                    hi = val;
            }
        vector<Integer> alphabet;
        for (auto val = lo; val <= hi; ++val)
            alphabet.push_back(val);

        auto nfa = regex_to_nfa(*_regex, alphabet);
        _num_states = nfa.num_states;
        _transitions = move(nfa.transitions);
        _final_states = move(nfa.final_states);
        _symbols = symbols_of(_transitions);
    }

    _bridge = make_shared<Bridge>();
    _graph_idx = initial_state.add_constraint_state(RegularGraph(static_cast<long>(_vars.size()), _num_states));
    _dead_cache_idx = initial_state.add_constraint_state(DeadCache{vector<set<long>>(_vars.size() + 1)});

    // Build the OPB alphabet: the union of transition keys and each var's initial
    // domain. Domain values absent from every transition get a "no transition"
    // constraint emitted below, which is what veripb needs to verify the
    // propagator's RUP-justified pruning of those values.
    _opb_alphabet.insert(_symbols.begin(), _symbols.end());
    for (const auto & var : _vars)
        for (const auto & val : initial_state.each_value_immutable(var))
            _opb_alphabet.insert(val);

    return true;
}

auto Regular::define_proof_model(ProofModel & model) -> void
{
    // state_at_pos_flags[i][q] means "after reading the first i symbols, the
    // automaton's chosen accepting run is in state q". Layer i takes input
    // vars[i] and produces layer i+1, with an extra row for the final state.
    auto & flags = _bridge->state_at_pos_flags;
    for (size_t idx = 0; idx <= _vars.size(); ++idx) {
        WPBSum exactly_1_true{};
        flags.emplace_back();
        for (long q = 0; q < _num_states; ++q) {
            // cake_pb_cp names the "in state q at position idx" flag x[id][idx_q][st];
            // match it so the proof's state literals line up with cake's OPB.
            flags[idx].emplace_back(
                model.create_proof_flag(_constraint_id, vector<long long>{static_cast<long long>(idx), static_cast<long long>(q)}, "st"));
            exactly_1_true += 1_i * flags[idx][q];
        }
        model.add_constraint(move(exactly_1_true) == 1_i);
    }

    // State at pos 0 is 0.
    model.add_constraint(WPBSum{} + 1_i * flags[0][0] >= 1_i);

    // State at pos n is one of the final states.
    WPBSum pos_n_states;
    for (const auto & f : _final_states)
        pos_n_states += 1_i * flags[_vars.size()][f];
    model.add_constraint(move(pos_n_states) >= 1_i);

    for (size_t idx = 0; idx < _vars.size(); ++idx) {
        for (long q = 0; q < _num_states; ++q) {
            for (const auto & val : _opb_alphabet) {
                const auto & targets = find_transitions(_transitions[q], val);
                if (targets.empty()) {
                    // No transition for (q, val), so constrain ~(state_i = q /\ X_i = val).
                    model.add_constraint(WPBSum{} + 1_i * (_vars[idx] != val) + 1_i * ! flags[idx][q] >= 1_i);
                }
                else {
                    // state_i = q /\ X_i = val implies state_{i+1} is one of the
                    // targets (a single target for a DFA, several for an NFA).
                    auto clause = WPBSum{} + 1_i * ! flags[idx][q] + 1_i * (_vars[idx] != val);
                    for (const auto & new_q : targets)
                        clause += 1_i * flags[idx + 1][new_q];
                    model.add_constraint(move(clause) >= 1_i);
                }
            }
        }
    }
}

auto Regular::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    // Top-level scaffolding: per-val backward chains and static dead-state lines,
    // derived once from the OPB encoding at search root. Pre-populates the
    // per-subtree DeadCache so the propagator skips re-emission for
    // statically-dead states. In assertion mode the per-call inferences are
    // asserted under the typed hint, so the scaffolding is wasted output.
    propagators.install_initialiser([vars = _vars, ns = _num_states, t = _transitions, fs = _final_states, bridge = _bridge,
                                        dead_cache_handle = _dead_cache_idx](State & state, auto &, ProofLogger * const logger) -> void {
        if (! logger || logger->get_assertion_level() != AssertionLevel::Off)
            return;
        bridge->static_dead = compute_static_dead(vars, ns, t, fs, state);
        emit_top_scaffolding(logger, vars, ns, t, bridge->state_at_pos_flags, state, bridge->static_dead);
        auto & cache = any_cast<DeadCache &>(state.get_constraint_state(dead_cache_handle));
        for (size_t i = 0; i < bridge->static_dead.size(); ++i)
            cache.dead[i].insert(bridge->static_dead[i].begin(), bridge->static_dead[i].end());
    });

    // Whole-scope declarative reason built once and captured; only its per-wake
    // eager materialisation stays in propagate_regular (see
    // dev_docs/propagator-performance.md).
    auto vars_reason = generic_reason(_vars);
    propagators.install(
        constraint_id(),
        [v = _vars, ns = _num_states, t = _transitions, fs = _final_states, g = _graph_idx, dc = _dead_cache_idx, bridge = _bridge,
            owner = constraint_id(),
            reason = std::move(vars_reason)](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            propagate_regular(v, ns, t, fs, bridge->state_at_pos_flags, g, dc, state, inference, logger, owner, reason);
            return PropagatorState::Enable;
        },
        triggers);
}

auto Regular::constraint_type() const -> std::string
{
    return "regular";
}

auto Regular::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    vector<SExpr> vars;
    for (const auto & var : _vars)
        vars.push_back(tracker.s_expr_term_of(var));

    // A regex-built Regular only compiles its automaton in prepare(), and prepare
    // runs on the installed clone, never on the stored constraint this is called
    // on -- so without compiling here too, the written .scp would describe an
    // empty automaton rather than the constraint actually solved (issue #481).
    // Rebuild the same alphabet prepare() uses: the contiguous min..max range
    // over the variables' initial domains, whose extremes are exactly the bounds
    // the tracker recorded at variable set-up.
    long num_states = _num_states;
    const auto * transitions = &_transitions;
    const auto * final_states = &_final_states;
    RegexNfa compiled{};
    if (_regex && 0 == num_states) {
        auto lo = Integer::max_value(), hi = Integer::min_value();
        for (const auto & var : _vars) {
            auto [l, u] = overloaded{[&](const SimpleIntegerVariableID & v) -> pair<Integer, Integer> { return tracker.tracked_bounds(v); },
                [&](const ViewOfIntegerVariableID & v) -> pair<Integer, Integer> {
                    auto [al, au] = tracker.tracked_bounds(v.actual_variable);
                    if (v.negate_first)
                        return {-au + v.then_add, -al + v.then_add};
                    return {al + v.then_add, au + v.then_add};
                },
                [&](const ConstantIntegerVariableID & v) -> pair<Integer, Integer> {
                    return {v.const_value, v.const_value};
                }}.visit(var);
            lo = min(lo, l);
            hi = max(hi, u);
        }
        vector<Integer> alphabet;
        for (auto val = lo; val <= hi; ++val)
            alphabet.push_back(val);
        compiled = regex_to_nfa(*_regex, alphabet);
        num_states = compiled.num_states;
        transitions = &compiled.transitions;
        final_states = &compiled.final_states;
    }

    // One edge list per state, in state order: position i holds the edges out of
    // state i, and each edge is (symbol target) -- reading `symbol` moves from
    // state i to state `target`. This is the shape cake_pb_cp's regular parser
    // expects. A non-deterministic automaton emits several edges with the same
    // symbol. The transitions are unordered_maps, so collect the (symbol, target)
    // pairs and sort them: the written .scp must be byte-stable across standard
    // libraries.
    vector<SExpr> states;
    for (long i = 0; i < num_states; ++i) {
        vector<SExpr> edges;
        if (static_cast<size_t>(i) < transitions->size()) {
            vector<pair<Integer, long>> sorted_edges;
            for (const auto & tran : (*transitions)[i])
                for (const auto & target : tran.second)
                    sorted_edges.emplace_back(tran.first, target);
            sort(sorted_edges);
            for (const auto & [sym, target] : sorted_edges)
                edges.push_back(SExpr::list({SExpr::atom(sym.to_string()), SExpr::atom(std::to_string(target))}));
        }
        states.push_back(SExpr::list(move(edges)));
    }

    vector<SExpr> finals;
    for (const auto & f : *final_states)
        finals.push_back(SExpr::atom(std::to_string(f)));

    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(vars)),
        SExpr::atom(std::to_string(num_states)), SExpr::list(move(states)), SExpr::list(move(finals))});
}
