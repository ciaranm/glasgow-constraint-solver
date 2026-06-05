#include <gcs/constraints/regular/regex.hh>
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
#include <cstdio>
#include <functional>
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
using std::ios;
using std::move;
using std::nullopt;
using std::optional;
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
        const State &, const ReasonFunction & reason, string comment = "") -> void
    {
        if (logger) {
            // Trying to cut down on repeated code
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

    auto initialise_graph(RegularGraph & graph, const vector<IntegerVariableID> & vars,
        const long num_states, const vector<unordered_map<Integer, set<long>>> & transitions,
        const vector<long> & final_states, const vector<vector<ProofFlag>> & state_at_pos_flags,
        const State & state, const ReasonFunction & reason, ProofLogger * const logger)
    {
        auto num_vars = vars.size();

        if (logger)
            logger->emit_proof_comment("Initialising graph");

        // Forward phase: accumulate
        graph.nodes[0].insert(0);
        for (unsigned long i = 0; i < num_vars; ++i) {
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

    auto decrement_outdeg(RegularGraph & graph, const long i, const long k, const vector<IntegerVariableID> & vars,
        const vector<vector<ProofFlag>> & state_at_pos_flags, const State & state, const ReasonFunction & reason, ProofLogger * const logger) -> void
    {
        graph.out_deg[i][k]--;
        if (graph.out_deg[i][k] == 0 && i > 0) {
            for (const auto & edge : graph.in_edges[i][k]) {
                auto l = edge.first;
                graph.out_edges[i - 1][l].erase(k);
                for (const auto & val : edge.second) {
                    // For an NFA, l may still reach a live state on val via
                    // another edge; only drop support (and justify doing so)
                    // once no such edge remains.
                    if (! still_supports(graph, i - 1, l, val)) {
                        graph.states_supporting[i - 1][val].erase(l);
                        if (logger)
                            log_additional_inference(logger, {vars[i - 1] != val}, {! state_at_pos_flags[i - 1][l]}, state, reason,
                                "dec outdeg inner");
                    }
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
        const State & state, const ReasonFunction & reason, ProofLogger * const logger) -> void
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
        const vector<unordered_map<Integer, set<long>>> & transitions,
        const vector<long> & final_states,
        const vector<vector<ProofFlag>> & state_at_pos_flags,
        const ConstraintStateHandle & graph_handle,
        const State & state,
        auto & inference,
        ProofLogger * const logger,
        const bool short_reasons) -> void
    {
        auto & graph = any_cast<RegularGraph &>(state.get_constraint_state(graph_handle));
        auto gen_reason = generic_reason(state, vars);

        ReasonFunction reason;
        ProofLine reason_definition_1, reason_definition_2;

        if (logger && short_reasons) {
            auto reason_sum = WPBSum{};
            for (const auto & lit : gen_reason()) {
                reason_sum += 1_i * get<ProofLiteral>(lit);
            }
            // We will manually delete this later.
            auto [_reason_short, _line1, _line2] =
                logger->create_proof_flag_reifying(reason_sum >= Integer(reason_sum.terms.size()), "", ProofLevel::Top);
            ProofFlag reason_short = _reason_short;
            reason_definition_1 = _line1;
            reason_definition_2 = _line2;
            reason = singleton_reason(reason_short);
        }
        else {
            reason = gen_reason;
        }

        if (! graph.initialised)
            initialise_graph(graph, vars, num_states, transitions, final_states, state_at_pos_flags, state, reason, logger);

        for (size_t i = 0; i < graph.states_supporting.size(); i++) {
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

                            decrement_outdeg(graph, i, q, vars, state_at_pos_flags, state, reason, logger);
                            decrement_indeg(graph, i + 1, next_q, vars, state_at_pos_flags, state, reason, logger);
                        }
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

        // // Need to check later whether this is safe to do now we have enumeration proofs
        // if (logger && short_reasons) {
        //     if (short_reasons) {
        //         logger->delete_range(reason_definition_1, reason_definition_2 + 1);
        //     }
        // }
    }
}

namespace
{
    // Records the alphabet (sorted transition keys) for proof logging and s_exprify.
    auto symbols_of(const vector<unordered_map<Integer, set<long>>> & transitions) -> vector<Integer>
    {
        set<Integer> sym_set;
        for (const auto & state_map : transitions)
            for (const auto & [val, _] : state_map)
                sym_set.insert(val);
        return {sym_set.begin(), sym_set.end()};
    }
}

Regular::Regular(vector<IntegerVariableID> v, long n, vector<unordered_map<Integer, long>> t, vector<long> f, bool sr) :
    _vars(move(v)),
    _num_states(n),
    _transitions(t.size()),
    _final_states(move(f)),
    _short_reasons(sr),
    _regex(nullopt)
{
    for (size_t q = 0; q < t.size(); ++q)
        for (const auto & [val, target] : t[q])
            if (target != -1L)
                _transitions[q][val].insert(target);
    _symbols = symbols_of(_transitions);
}

Regular::Regular(vector<IntegerVariableID> v, long n, vector<vector<long>> transitions, vector<long> f, bool sr) :
    _vars(move(v)),
    _num_states(n),
    _transitions(n),
    _final_states(move(f)),
    _short_reasons(sr),
    _regex(nullopt)
{
    for (size_t i = 0; i < transitions.size(); i++)
        for (size_t j = 0; j < transitions[i].size(); j++)
            if (transitions[i][j] != -1L)
                _transitions[i][Integer(j)].insert(transitions[i][j]);
    _symbols = symbols_of(_transitions);
}

Regular::Regular(vector<IntegerVariableID> v, string regex, bool sr) :
    _vars(move(v)),
    _num_states(0),
    _short_reasons(sr),
    _regex(move(regex))
{
    // The automaton is compiled from the regex in prepare(), once the
    // variables' domains (and hence the alphabet for "." and "[^...]") are known.
}

Regular::Regular(vector<IntegerVariableID> v, long n, vector<unordered_map<Integer, set<long>>> t,
    vector<long> f, vector<Integer> syms, bool sr, optional<string> regex) :
    _vars(move(v)),
    _num_states(n),
    _transitions(move(t)),
    _final_states(move(f)),
    _short_reasons(sr),
    _regex(move(regex)),
    _symbols(move(syms))
{
}

auto Regular::symbols() const -> const vector<Integer> &
{
    return _symbols;
}

auto Regular::clone() const -> unique_ptr<Constraint>
{
    return unique_ptr<Constraint>(new Regular(_vars, _num_states, _transitions, _final_states, _symbols, _short_reasons, _regex));
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

    _graph_idx = initial_state.add_constraint_state(RegularGraph(_vars.size(), _num_states));

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
    // Make 2D array of flags: state_at_pos_flags[i][q] means the DFA is in state q when it receives the
    // input value from vars[i], with an extra row of flags for the state after the last transition.
    // NB: Might be easier to have a 1D array of ProofOnlyIntegerVariables, but making literals of these is
    // awkward currently. (TODO ?)
    for (size_t idx = 0; idx <= _vars.size(); ++idx) {
        WPBSum exactly_1_true{};
        _state_at_pos_flags.emplace_back();
        for (long q = 0; q < _num_states; ++q) {
            _state_at_pos_flags[idx].emplace_back(model.create_proof_flag(format("state{}is{}", idx, q)));
            exactly_1_true += 1_i * _state_at_pos_flags[idx][q];
        }
        model.add_constraint(move(exactly_1_true) == 1_i);
    }

    // State at pos 0 is 0
    model.add_constraint(WPBSum{} + 1_i * _state_at_pos_flags[0][0] >= 1_i);
    // State at pos n is one of the final states
    WPBSum pos_n_states;
    for (const auto & f : _final_states) {
        pos_n_states += 1_i * _state_at_pos_flags[_vars.size()][f];
    }
    model.add_constraint(move(pos_n_states) >= 1_i);

    for (size_t idx = 0; idx < _vars.size(); ++idx) {
        for (long q = 0; q < _num_states; ++q) {
            for (const auto & val : _opb_alphabet) {
                const auto & targets = find_transitions(_transitions[q], val);
                if (targets.empty()) {
                    // No transition for (q, val), so constrain ~(state_i = q /\ X_i = val)
                    model.add_constraint(
                        WPBSum{} + 1_i * (_vars[idx] != val) + (1_i * ! _state_at_pos_flags[idx][q]) >= 1_i);
                }
                else {
                    // state_i = q /\ X_i = val implies state_{i+1} is one of the
                    // targets (a single target for a DFA, several for an NFA).
                    auto clause = WPBSum{} + 1_i * ! _state_at_pos_flags[idx][q] + 1_i * (_vars[idx] != val);
                    for (const auto & new_q : targets)
                        clause += 1_i * _state_at_pos_flags[idx + 1][new_q];
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

    propagators.install([v = move(_vars), n = _num_states, t = move(_transitions), f = move(_final_states), g = _graph_idx, flags = move(_state_at_pos_flags), sr = _short_reasons](
                            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
        propagate_regular(v, n, t, f, flags, g, state, inference, logger, sr);
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
    for (size_t i = 0; i < _transitions.size(); i++) {
        print(s, "(");
        for (const auto & tran : _transitions[i]) {
            for (const auto & target : tran.second)
                print(s, " ({} {})", tran.first, target);
        }
        print(s, ")\n        ");
    }
    print(s, "))\n       (");
    for (const auto & f : _final_states)
        print(s, " {}", f);
    print(s, ")");

    return s.str();
}
